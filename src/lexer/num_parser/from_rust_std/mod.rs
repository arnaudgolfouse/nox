//! Decimal floats parsing.
//!
//! Directly taken from rust's std source code, with some simplification :
//! macros have been replaced by their result, and f32 code was removed.
//!
//! Only allow parsing of decimal floats...

#![allow(clippy::many_single_char_names)]

mod algorithm;
mod bignum;
mod diy_float;
mod num;
mod rawfp;
mod table;

use super::Decimal;
use num::digits_to_big;
use rawfp::RawFloat;
use std::convert::TryFrom;

pub struct DecimalFloat<'a> {
    pub integral: &'a [u8],
    pub fractional: &'a [u8],
    pub exp: i64,
}

impl<'a> TryFrom<Decimal<'a>> for DecimalFloat<'a> {
    type Error = ();
    fn try_from(decimal: Decimal<'a>) -> Result<Self, <Self as TryFrom<Decimal>>::Error> {
        match decimal.fractional {
            Some(fractional) => Ok(Self {
                integral: decimal.integral,
                fractional,
                exp: decimal.exp,
            }),
            None => Err(()),
        }
    }
}

type Big = bignum::Big32x40;

/// The main workhorse for the decimal-to-float conversion: Orchestrate all the preprocessing
/// and figure out which algorithm should do the actual conversion.
pub fn convert(mut decimal: DecimalFloat<'_>) -> Result<f64, ParseFloatError> {
    simplify(&mut decimal);
    if let Some(x) = trivial_cases(&decimal) {
        return Ok(x);
    }
    // Remove/shift out the decimal point.
    let e = decimal.exp - decimal.fractional.len() as i64;
    if let Some(x) = algorithm::fast_path(decimal.integral, decimal.fractional, e) {
        return Ok(x);
    }
    // Big32x40 is limited to 1280 bits, which translates to about 385 decimal digits.
    // If we exceed this, we'll crash, so we error out before getting too close (within 10^10).
    let upper_bound = bound_intermediate_digits(&decimal, e);
    if upper_bound > 375 {
        return Err(ParseFloatError::Invalid);
    }
    let f = digits_to_big(decimal.integral, decimal.fractional);

    // Now the exponent certainly fits in 16 bit, which is used throughout the main algorithms.
    let e = e as i16;
    // FIXME These bounds are rather conservative. A more careful analysis of the failure modes
    // of Bellerophon could allow using it in more cases for a massive speed up.
    let exponent_in_range = table::MIN_E <= e && e <= table::MAX_E;
    let value_in_range = upper_bound <= <f64 as RawFloat>::MAX_NORMAL_DIGITS as u64;
    if exponent_in_range && value_in_range {
        Ok(algorithm::bellerophon(&f, e))
    } else {
        Ok(algorithm::algorithm_m(&f, e))
    }
}

// As written, this optimizes badly (see #27130, though it refers to an old version of the code).
// `inline(always)` is a workaround for that. There are only two call sites overall and it doesn't
// make code size worse.

/// Strip zeros where possible, even when this requires changing the exponent
#[inline(always)]
fn simplify(decimal: &mut DecimalFloat<'_>) {
    let is_zero = &|&&d: &&u8| -> bool { d == b'0' };
    // Trimming these zeros does not change anything but may enable the fast path (< 15 digits).
    let leading_zeros = decimal.integral.iter().take_while(is_zero).count();
    decimal.integral = &decimal.integral[leading_zeros..];
    let trailing_zeros = decimal.fractional.iter().rev().take_while(is_zero).count();
    let end = decimal.fractional.len() - trailing_zeros;
    decimal.fractional = &decimal.fractional[..end];
    // Simplify numbers of the form 0.0...x and x...0.0, adjusting the exponent accordingly.
    // This may not always be a win (possibly pushes some numbers out of the fast path), but it
    // simplifies other parts significantly (notably, approximating the magnitude of the value).
    if decimal.integral.is_empty() {
        let leading_zeros = decimal.fractional.iter().take_while(is_zero).count();
        decimal.fractional = &decimal.fractional[leading_zeros..];
        decimal.exp -= leading_zeros as i64;
    } else if decimal.fractional.is_empty() {
        let trailing_zeros = decimal.integral.iter().rev().take_while(is_zero).count();
        let end = decimal.integral.len() - trailing_zeros;
        decimal.integral = &decimal.integral[..end];
        decimal.exp += trailing_zeros as i64;
    }
}

/// Returns a quick-an-dirty upper bound on the size (log10) of the largest value that Algorithm R
/// and Algorithm M will compute while working on the given decimal.
fn bound_intermediate_digits(decimal: &DecimalFloat<'_>, e: i64) -> u64 {
    // We don't need to worry too much about overflow here thanks to trivial_cases() and the
    // parser, which filter out the most extreme inputs for us.
    let f_len: u64 = decimal.integral.len() as u64 + decimal.fractional.len() as u64;
    if e >= 0 {
        // In the case e >= 0, both algorithms compute about `f * 10^e`. Algorithm R proceeds to
        // do some complicated calculations with this but we can ignore that for the upper bound
        // because it also reduces the fraction beforehand, so we have plenty of buffer there.
        f_len + (e as u64)
    } else {
        // If e < 0, Algorithm R does roughly the same thing, but Algorithm M differs:
        // It tries to find a positive number k such that `f << k / 10^e` is an in-range
        // significand. This will result in about `2^53 * f * 10^e` < `10^17 * f * 10^e`.
        // One input that triggers this is 0.33...33 (375 x 3).
        f_len + (e.abs() as u64) + 17
    }
}

/// Detects obvious overflows and underflows without even looking at the decimal digits.
fn trivial_cases(decimal: &DecimalFloat<'_>) -> Option<f64> {
    // There were zeros but they were stripped by simplify()
    if decimal.integral.is_empty() && decimal.fractional.is_empty() {
        return Some(0.0);
    }
    // This is a crude approximation of ceil(log10(the real value)). We don't need to worry too
    // much about overflow here because the input length is tiny (at least compared to 2^64) and
    // the parser already handles exponents whose absolute value is greater than 10^18
    // (which is still 10^19 short of 2^64).
    let max_place = decimal.exp + decimal.integral.len() as i64;
    if max_place > <f64 as RawFloat>::INF_CUTOFF {
        return Some(f64::INFINITY);
    } else if max_place < <f64 as RawFloat>::ZERO_CUTOFF {
        return Some(0.0);
    }
    None
}

pub enum ParseFloatError {
    Empty,
    Invalid,
}

//! Bit fiddling on positive IEEE 754 floats. Negative numbers aren't and needn't be handled.
//! Normal floating point numbers have a canonical representation as (frac, exp) such that the
//! value is 2<sup>exp</sup> * (1 + sum(frac[N-i] / 2<sup>i</sup>)) where N is the number of bits.
//! Subnormals are slightly different and weird, but the same principle applies.
//!
//! Here, however, we represent them as (sig, k) with f positive, such that the value is f *
//! 2<sup>e</sup>. Besides making the "hidden bit" explicit, this changes the exponent by the
//! so-called mantissa shift.
//!
//! Put another way, normally floats are written as (1) but here they are written as (2):
//!
//! 1. `1.101100...11 * 2^m`
//! 2. `1101100...11 * 2^n`
//!
//! We call (1) the **fractional representation** and (2) the **integral representation**.
//!
//! Many functions in this module only handle normal numbers. The dec2flt routines conservatively
//! take the universally-correct slow path (Algorithm M) for very small and very large numbers.
//! That algorithm needs only next_float() which does handle subnormals and zeros.
use super::diy_float::Fp;
use super::table;
use super::Big;
use std::cmp::Ordering::{Equal, Greater, Less};
use std::convert::TryFrom;
use std::fmt::{Debug, LowerExp};
use std::num::FpCategory;
use std::num::FpCategory::{Infinite, Nan, Normal, Subnormal, Zero};
use std::ops::{Add, Div, Mul, Neg};

#[derive(Copy, Clone, Debug)]
pub(super) struct Unpacked {
    pub(super) sig: u64,
    pub(super) k: i16,
}

impl Unpacked {
    pub(super) fn new(sig: u64, k: i16) -> Self {
        Unpacked { sig, k }
    }
}

/// A helper trait to avoid duplicating basically all the conversion code for `f32` and `f64`.
///
/// See the parent module's doc comment for why this is necessary.
///
/// Should **never ever** be implemented for other types or be used outside the dec2flt module.
pub(super) trait RawFloat:
    Copy + Debug + LowerExp + Mul<Output = Self> + Div<Output = Self> + Neg<Output = Self>
{
    /// Type used by `to_bits` and `from_bits`.
    type Bits: Add<Output = Self::Bits> + From<u8> + TryFrom<u64>;

    /// Returns the category that this number falls into.
    fn classify(self) -> FpCategory;

    /// Returns the mantissa, exponent and sign as integers.
    fn integer_decode(self) -> (u64, i16, i8);

    /// Decodes the float.
    fn unpack(self) -> Unpacked;

    /// Casts from a small integer that can be represented exactly. Panic if the integer can't be
    /// represented, the other code in this module makes sure to never let that happen.
    fn from_int(x: u64) -> Self;

    /// Gets the value 10<sup>e</sup> from a pre-computed table.
    /// Panics for `e >= CEIL_LOG5_OF_MAX_SIG`.
    fn short_fast_pow10(e: usize) -> Self;

    /// What the name says. It's easier to hard code than juggling intrinsics and
    /// hoping LLVM constant folds it.
    const CEIL_LOG5_OF_MAX_SIG: i16;

    // A conservative bound on the decimal digits of inputs that can't produce overflow or zero or
    /// subnormals. Probably the decimal exponent of the maximum normal value, hence the name.
    const MAX_NORMAL_DIGITS: usize;

    /// When the most significant decimal digit has a place value greater than this, the number
    /// is certainly rounded to infinity.
    const INF_CUTOFF: i64;

    /// When the most significant decimal digit has a place value less than this, the number
    /// is certainly rounded to zero.
    const ZERO_CUTOFF: i64;

    /// The number of bits in the exponent.
    const EXP_BITS: u8;

    /// The number of bits in the significand, *including* the hidden bit.
    const SIG_BITS: u8;

    /// The number of bits in the significand, *excluding* the hidden bit.
    const EXPLICIT_SIG_BITS: u8;

    /// The maximum legal exponent in fractional representation.
    const MAX_EXP: i16;

    /// The minimum legal exponent in fractional representation, excluding subnormals.
    const MIN_EXP: i16;

    /// `MAX_EXP` for integral representation, i.e., with the shift applied.
    const MAX_EXP_INT: i16;

    /// `MAX_EXP` encoded (i.e., with offset bias)
    const MAX_ENCODED_EXP: i16;

    /// `MIN_EXP` for integral representation, i.e., with the shift applied.
    const MIN_EXP_INT: i16;

    /// The maximum normalized significand in integral representation.
    const MAX_SIG: u64;

    /// The minimal normalized significand in integral representation.
    const MIN_SIG: u64;
}

impl RawFloat for f64 {
    type Bits = u64;

    const SIG_BITS: u8 = 53;
    const EXP_BITS: u8 = 11;
    const CEIL_LOG5_OF_MAX_SIG: i16 = 23;
    const MAX_NORMAL_DIGITS: usize = 305;
    const INF_CUTOFF: i64 = 310;
    const ZERO_CUTOFF: i64 = -326;
    const EXPLICIT_SIG_BITS: u8 = Self::SIG_BITS - 1;
    const MAX_EXP: i16 = (1 << (Self::EXP_BITS - 1)) - 1;
    const MIN_EXP: i16 = -<Self as RawFloat>::MAX_EXP + 1;
    const MAX_EXP_INT: i16 = <Self as RawFloat>::MAX_EXP - (Self::SIG_BITS as i16 - 1);
    const MAX_ENCODED_EXP: i16 = (1 << Self::EXP_BITS) - 1;
    const MIN_EXP_INT: i16 = <Self as RawFloat>::MIN_EXP - (Self::SIG_BITS as i16 - 1);
    const MAX_SIG: u64 = (1 << Self::SIG_BITS) - 1;
    const MIN_SIG: u64 = 1 << (Self::SIG_BITS - 1);

    /// Returns the mantissa, exponent and sign as integers.
    fn integer_decode(self) -> (u64, i16, i8) {
        let bits = self.to_bits();
        let sign: i8 = if bits >> 63 == 0 { 1 } else { -1 };
        let mut exponent: i16 = ((bits >> 52) & 0x7ff) as i16;
        let mantissa = if exponent == 0 {
            (bits & 0xfffffffffffff) << 1
        } else {
            (bits & 0xfffffffffffff) | 0x10000000000000
        };
        // Exponent bias + mantissa shift
        exponent -= 1023 + 52;
        (mantissa, exponent, sign)
    }

    fn unpack(self) -> Unpacked {
        let (sig, exp, _sig) = self.integer_decode();
        Unpacked::new(sig, exp)
    }

    #[allow(clippy::float_cmp)]
    fn from_int(x: u64) -> f64 {
        // rkruppe is uncertain whether `as` rounds correctly on all platforms.
        debug_assert!(x as f64 == fp_to_float(Fp { f: x, e: 0 }));
        x as f64
    }

    fn short_fast_pow10(e: usize) -> Self {
        table::F64_SHORT_POWERS[e]
    }

    fn classify(self) -> FpCategory {
        self.classify()
    }
}

/// Converts an `Fp` to the closest machine float type.
pub(super) fn fp_to_float(x: Fp) -> f64 {
    let x = x.normalize();
    // x.f is 64 bit, so x.e has a mantissa shift of 63
    let e = x.e + 63;
    debug_assert!(
        e <= <f64 as RawFloat>::MAX_EXP,
        "fp_to_float: exponent {} too large",
        e
    );
    debug_assert!(
        e >= <f64 as RawFloat>::MIN_EXP,
        "fp_to_float: exponent {} too small",
        e
    );

    encode_normal(round_normal(x))
}

/// Round the 64-bit significand to T::SIG_BITS bits with half-to-even.
/// Does not handle exponent overflow.
fn round_normal(x: Fp) -> Unpacked {
    let excess = 64 - <f64 as RawFloat>::SIG_BITS as i16;
    let half: u64 = 1 << (excess - 1);
    let (q, rem) = (x.f >> excess, x.f & ((1 << excess) - 1));
    debug_assert_eq!(q << excess | rem, x.f);
    // Adjust mantissa shift
    let k = x.e + excess;
    if rem < half || (rem == half && (q % 2) == 0) {
        Unpacked::new(q, k)
    } else if q == <f64 as RawFloat>::MAX_SIG {
        Unpacked::new(<f64 as RawFloat>::MIN_SIG, k + 1)
    } else {
        Unpacked::new(q + 1, k)
    }
}

/// Inverse of `RawFloat::unpack()` for normalized numbers.
/// Panics if the significand or exponent are not valid for normalized numbers.
pub(super) fn encode_normal(x: Unpacked) -> f64 {
    debug_assert!(
        <f64 as RawFloat>::MIN_SIG <= x.sig && x.sig <= <f64 as RawFloat>::MAX_SIG,
        "encode_normal: significand not normalized"
    );
    // Remove the hidden bit
    let sig_enc = x.sig & !(1 << <f64 as RawFloat>::EXPLICIT_SIG_BITS);
    // Adjust the exponent for exponent bias and mantissa shift
    let k_enc = x.k + <f64 as RawFloat>::MAX_EXP + <f64 as RawFloat>::EXPLICIT_SIG_BITS as i16;
    debug_assert!(
        k_enc != 0 && k_enc < <f64 as RawFloat>::MAX_ENCODED_EXP,
        "encode_normal: exponent out of range"
    );
    // Leave sign bit at 0 ("+"), our numbers are all positive
    let bits = (k_enc as u64) << <f64 as RawFloat>::EXPLICIT_SIG_BITS | sig_enc;
    f64::from_bits(bits)
}

/// Approximate a bignum with an Fp. Rounds within 0.5 ULP with half-to-even.
pub(super) fn big_to_fp(f: &Big) -> Fp {
    let end = f.bit_length();
    debug_assert!(end != 0, "big_to_fp: unexpectedly, input is zero");
    let start = end.saturating_sub(64);
    let leading = super::num::get_bits(f, start, end);
    // We cut off all bits prior to the index `start`, i.e., we effectively right-shift by
    // an amount of `start`, so this is also the exponent we need.
    let e = start as i16;
    let rounded_down = Fp { f: leading, e }.normalize();
    // Round (half-to-even) depending on the truncated bits.
    match super::num::compare_with_half_ulp(f, start) {
        Less => rounded_down,
        Equal if leading % 2 == 0 => rounded_down,
        Equal | Greater => match leading.checked_add(1) {
            Some(f) => Fp { f, e }.normalize(),
            None => Fp {
                f: 1 << 63,
                e: e + 1,
            },
        },
    }
}

/// Finds the largest floating point number strictly smaller than the argument.
/// subnormals, zero, or exponent underflow are just returned.
pub(super) fn prev_float(x: f64) -> f64 {
    match x.classify() {
        Infinite | Nan | Subnormal | Zero => x,
        Normal => {
            let Unpacked { sig, k } = x.unpack();
            if sig == <f64 as RawFloat>::MIN_SIG {
                encode_normal(Unpacked::new(<f64 as RawFloat>::MAX_SIG, k - 1))
            } else {
                encode_normal(Unpacked::new(sig - 1, k))
            }
        }
    }
}

// Find the smallest floating point number strictly larger than the argument.
// This operation is saturating, i.e., next_float(inf) == inf.
// Unlike most code in this module, this function does handle zero, subnormals, and infinities.
// Nan is just returned however.
pub(super) fn next_float(x: f64) -> f64 {
    match x.classify() {
        Nan => x,
        Infinite => f64::INFINITY,
        // This seems too good to be true, but it works.
        // 0.0 is encoded as the all-zero word. Subnormals are 0x000m...m where m is the mantissa.
        // In particular, the smallest subnormal is 0x0...01 and the largest is 0x000F...F.
        // The smallest normal number is 0x0010...0, so this corner case works as well.
        // If the increment overflows the mantissa, the carry bit increments the exponent as we
        // want, and the mantissa bits become zero. Because of the hidden bit convention, this
        // too is exactly what we want!
        // Finally, f64::MAX + 1 = 7eff...f + 1 = 7ff0...0 = f64::INFINITY.
        Zero | Subnormal | Normal => {
            f64::from_bits(x.to_bits() + <f64 as RawFloat>::Bits::from(1u8))
        }
    }
}

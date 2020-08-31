//! f64 representation :
//!
//! sign - exponent - mantissa
//! 1    - 11       - 52

// number ::= "0x" ~ hexadigit+ ~ ( . ~ hexadigit* )?
//
//     | "0o" ~ octadigit+ ~ ( . ~ octadigit* )?
//
//     | "0o" ~ binarydigit+ ~ ( . ~ binarydigit* )?
//
//     | digit* ~ ( . ~ digit* )? ~ ( ("e" | "E") ~ ("+" | "-")? ~ digit* )?
//

mod from_rust_std;

use super::Warning;
use from_rust_std::{DecimalFloat, ParseFloatError};
use std::{convert::TryFrom, fmt};

#[derive(Clone, Debug, Copy, PartialEq)]
pub enum IntOrFloat {
    Int(i64),
    Float(f64),
}

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub enum Sign {
    Positive,
    Negative,
}

#[derive(Clone, Debug, Copy, PartialEq, Eq, PartialOrd)]
#[repr(u64)]
pub enum Base {
    Binary = 2,
    Octal = 8,
    Decimal = 10,
    Hexadecimal = 16,
}

impl Base {
    pub fn as_i64(self) -> i64 {
        self as i64
    }
}

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub struct Number<'a> {
    pub integral: &'a [u8],
    /// `None` if this is an integer (no '.')
    pub fractional: Option<&'a [u8]>,
}

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub struct Decimal<'a> {
    pub integral: &'a [u8],
    /// `None` if this is an integer (no '.' or 'e')
    pub fractional: Option<&'a [u8]>,
    /// The decimal exponent, guaranteed to have fewer than 18 decimal digits.
    pub exp: i64,
}

/// Extract the longest prefix from input where all elements match `predicate`.
///
/// If `predicate` returns `None`, an error is emitted with the faulty digit.
#[allow(clippy::type_complexity)] // for the result type
fn eat<F>(input: &[u8], mut predicate: F) -> Result<(&[u8], &[u8]), u8>
where
    F: FnMut(u8) -> Option<bool>,
{
    let mut position = 0;
    while let Some(c) = input.get(position).copied() {
        if predicate(c).ok_or(c)? {
            position += 1;
        } else {
            break;
        }
    }

    Ok((&input[..position], &input[position..]))
}

fn invalid_char(c: u8, base: Base) -> NumberError {
    if c == b'.' {
        NumberError::NumberUnexpectedDot
    } else {
        NumberError::Invalid(c as char, base)
    }
}

pub fn parse_number(number: &str) -> Result<(IntOrFloat, Option<Warning>), NumberError> {
    // we only reason on u8's
    let mut number = number.as_bytes();
    let sign = match number.get(0).copied() {
        Some(b'-') => {
            number = &number[1..];
            Sign::Negative
        }
        Some(_) => Sign::Positive,
        None => return Err(NumberError::Empty),
    };
    let base = match number.get(0).copied() {
        Some(b'0') => match number.get(1).copied() {
            Some(b'b') => {
                number = &number[2..];
                Base::Binary
            }
            Some(b'o') => {
                number = &number[2..];
                Base::Octal
            }
            Some(b'x') => {
                number = &number[2..];
                Base::Hexadecimal
            }
            _ => Base::Decimal,
        },
        Some(_) => Base::Decimal,
        None => return Err(NumberError::Empty),
    };

    parse_number_with_sign_base(number, sign, base)
}

/// Parse a number with the sign/base already parsed
pub fn parse_number_with_sign_base(
    number: &[u8],
    sign: Sign,
    base: Base,
) -> Result<(IntOrFloat, Option<Warning>), NumberError> {
    if let Base::Decimal = base {
        let decimal = decompose_decimal_number(number)?;
        // sigh... we must remove '_'
        let integral_vec = {
            let mut integral = Vec::new();
            for x in decimal.integral {
                if *x != b'_' {
                    integral.push(*x)
                }
            }
            integral
        };
        let mut fractional_vec = Vec::new();
        if let Some(dec_fractional) = decimal.fractional {
            for x in dec_fractional {
                if *x != b'_' {
                    fractional_vec.push(*x)
                }
            }
        }
        match DecimalFloat::try_from(Decimal {
            integral: &integral_vec,
            fractional: if decimal.fractional.is_some() {
                Some(&fractional_vec)
            } else {
                None
            },
            exp: decimal.exp,
        }) {
            Ok(float_decimal) => from_rust_std::convert(float_decimal)
                .map(|f| if sign == Sign::Negative { -f } else { f })
                .map(|f| (IntOrFloat::Float(f), None))
                .map_err(|err| err.into()),
            Err(()) => {
                parse_i64(decimal.integral, sign, Base::Decimal).map(|i| (IntOrFloat::Int(i), None))
            }
        }
    } else {
        let num = decompose_number(number, base)?;
        match num.fractional {
            Some(fractional) => parse_f64(num.integral, fractional, sign, base)
                .map(|(f, warn)| (IntOrFloat::Float(f), warn)),
            None => parse_i64(num.integral, sign, base).map(|i| (IntOrFloat::Int(i), None)),
        }
    }
}

/// Check that the given digit is valid for the given base, and return its value
/// as a `u8` if it is.
fn valid_for_base(c: u8, base: Base) -> Option<u8> {
    match c {
        b'0' | b'1' => Some(c - b'0'),
        b'2'..=b'7' if base >= Base::Octal => Some(c - b'0'),
        b'8' | b'9' if base >= Base::Decimal => Some(c - b'0'),
        b'a'..=b'f' if base >= Base::Hexadecimal => Some(c - b'a' + 10),
        b'A'..=b'F' if base >= Base::Hexadecimal => Some(c - b'A' + 10),
        _ => None,
    }
}

/// Sign and base already parsed
///
/// Decompose a number (floating-point or integral) into its integral and
/// fractional parts.
fn decompose_number(input: &[u8], base: Base) -> Result<Number, NumberError> {
    if input.is_empty() {
        return Err(NumberError::Empty);
    }

    let (integral, input) = eat(input, |c| match c {
        b'.' => Some(false),
        _ => {
            if c == b'_' || valid_for_base(c, base).is_some() {
                Some(true)
            } else {
                None
            }
        }
    })
    .map_err(|c| invalid_char(c, base))?;

    let fractional = match input.get(1..) {
        Some(input) => {
            eat(input, |c| {
                if c == b'_' || valid_for_base(c, base).is_some() {
                    Some(true)
                } else {
                    None
                }
            })
            .map_err(|c| invalid_char(c, base))?;
            if integral.is_empty() && input.is_empty() {
                return Err(NumberError::Empty);
            }
            Some(input)
        }
        None => None,
    };

    Ok(Number {
        integral,
        fractional,
    })
}

/// Sign already parsed
///
/// Decompose a decimal (floating-point or integral) number into its integral,
/// fractional and exponent parts.
fn decompose_decimal_number(mut input: &[u8]) -> Result<Decimal, NumberError> {
    if input.is_empty() {
        return Err(NumberError::Empty);
    }

    let integral = {
        let (integral, inp) = eat(input, |c| match c {
            b'.' | b'e' | b'E' => Some(false),
            b'0'..=b'9' | b'_' => Some(true),
            _ => None,
        })
        .map_err(|c| invalid_char(c, Base::Decimal))?;
        input = inp;
        integral
    };

    let fractional = match input.get(0) {
        Some(b'.') => {
            let (fractional, inp) = eat(&input[1..], |c| match c {
                b'e' | b'E' => Some(false),
                b'0'..=b'9' | b'_' => Some(true),
                _ => None,
            })
            .map_err(|c| invalid_char(c, Base::Decimal))?;
            input = inp;
            Some(fractional)
        }
        Some(b'e') | Some(b'E') => Some(&[] as _),
        _ => {
            return Ok(Decimal {
                integral,
                fractional: None,
                exp: 0,
            })
        }
    };

    match input.get(0) {
        Some(b'e') | Some(b'E') => {
            let sign = match *input.get(1).ok_or(NumberError::NoExponent)? {
                b'-' => {
                    input = &input[1..];
                    Sign::Negative
                }
                b'+' => {
                    input = &input[1..];
                    Sign::Positive
                }
                _ => Sign::Positive,
            };
            let mut exp = 0;
            let mut digit_number = 0;
            eat(&input[1..], |c| {
                if digit_number >= 18 {
                    digit_number += 1;
                    Some(false)
                } else {
                    match c {
                        b'_' => Some(true),
                        b'0'..=b'9' => {
                            digit_number += 1;
                            exp = exp * 10 + i64::from(c - b'0');
                            Some(true)
                        }
                        _ => None,
                    }
                }
            })
            .map_err(|c| invalid_char(c, Base::Decimal))?;

            if digit_number > 18 {
                return Err(NumberError::TooManyDigitsInExponent);
            }

            Ok(Decimal {
                integral,
                fractional,
                exp: if sign == Sign::Positive { exp } else { -exp },
            })
        }
        Some(_) => unreachable!(),
        None => Ok(Decimal {
            integral,
            fractional,
            exp: 0,
        }),
    }
}

/// We already have the sign and the base, let's do it !
fn parse_i64(input: &[u8], sign: Sign, base: Base) -> Result<i64, NumberError> {
    let mut result: i64 = 0;
    for c in input.iter().copied() {
        if c == b'_' {
            continue;
        }
        let digit =
            i64::from(valid_for_base(c, base).ok_or(NumberError::Invalid(c as char, base))?)
                * if sign == Sign::Negative { -1 } else { 1 };
        result = result
            .checked_mul(base.as_i64())
            .ok_or(NumberError::Overflow)?
            .checked_add(digit)
            .ok_or(NumberError::Overflow)?;
    }

    Ok(result)
}

/// Parse a floating point number for binary, octal and hexadecimal bases.
fn parse_f64(
    mut integral: &[u8],
    mut fractional: &[u8],
    sign: Sign,
    base: Base,
) -> Result<(f64, Option<Warning>), NumberError> {
    let log2 = match base {
        Base::Binary => 1,
        Base::Octal => 3,
        Base::Hexadecimal => 4,
        _ => unreachable!(),
    };
    let max_mantissa_digits = 52 / log2;

    // simplifications
    while integral.first().copied() == Some(b'0') {
        integral = &integral[1..];
    }
    while fractional.last().copied() == Some(b'0') {
        fractional = &fractional[..fractional.len() - 1]
    }

    Ok(if !integral.is_empty() {
        // exponent will be positive or zero

        let warning = if integral.len() > max_mantissa_digits {
            return Err(NumberError::FloatOverflow);
        } else if integral.len() + fractional.len() > max_mantissa_digits {
            fractional = &fractional[..max_mantissa_digits - integral.len()];
            Some(Warning::ExcessiveFloatPrecision)
        } else {
            None
        };
        // integral is non-empty here
        let pow = log2 * (integral.len() - 1)
            + match integral.first().copied().unwrap_or(0) {
                b'1' => 0,
                b'2' | b'3' => 1,
                b'4'..=b'7' => 2,
                _ => 3,
            };

        let sign = (sign == Sign::Negative) as u64;
        let exponent = 1023 + pow as u64;
        let mantissa = make_mantissa(integral, fractional, base);

        (
            f64::from_bits((sign << 63) | (exponent << 52) | mantissa),
            warning,
        )
    } else {
        // exponent will be strictly negative
        let mut pow = 0;
        while fractional.first().copied() == Some(b'0') {
            pow += log2;
            fractional = &fractional[1..]
        }

        // zero
        if fractional.is_empty() {
            return Ok((
                f64::from_bits(((sign == Sign::Negative) as u64) << 63),
                None,
            ));
        }

        // fractional is non-empty here
        pow += log2
            - match fractional.first().copied().unwrap_or(0) {
                0 => log2,
                b'1' => 0,
                b'2' | b'3' => 1,
                b'4'..=b'7' => 2,
                _ => 3,
            };

        let warning = if fractional.len() > max_mantissa_digits {
            fractional = &fractional[..max_mantissa_digits];
            Some(Warning::ExcessiveFloatPrecision)
        } else {
            None
        };

        let sign = (sign == Sign::Negative) as u64;
        let exponent = 1023 - pow as u64;
        let mantissa = make_mantissa(&fractional[0..1], &fractional[1..], base);

        (
            f64::from_bits((sign << 63) | (exponent << 52) | mantissa),
            warning,
        )
    })
}

/// Create a u64 containing the digits of `integral` and `fractional` in the
/// base `base`.
///
/// # Note
///
/// - `integral` should be non-empty and begin with a non-zero digit.
/// - The result should not overflow a u52.
/// - The first non-zero digit of the result will be cut off, because it is
/// implicit.
/// - No checks will be made to verify that `integral`/`fractional` contain only
/// valid digits.
fn make_mantissa(integral: &[u8], fractional: &[u8], base: Base) -> u64 {
    let byte_length = match base {
        Base::Binary => 1,
        Base::Octal => 3,
        Base::Hexadecimal => 4,
        _ => unreachable!(),
    };
    // where we start to write the digits.
    // this depends on the first digit, because the first bit is implicit and
    // should be cut off.
    let mut current_bit = 52
        - match integral.first().copied().unwrap_or(0) {
            b'1' => 0,
            b'2' | b'3' => 1,
            b'4'..=b'7' => 2,
            _ => 3,
        };
    let mut result = 0;

    for x in integral.iter().copied().chain(fractional.iter().copied()) {
        result |= u64::from(match x {
            b'0'..=b'9' => x - b'0',
            b'a'..=b'f' => x - b'a' + 10,
            b'A'..=b'F' => x - b'A' + 10,
            _ => 0,
        }) << current_bit;
        current_bit -= byte_length;
    }

    // cuts the first non-zero digit.
    result & 0x000f_ffff_ffff_ffff
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NumberError {
    /// No digits were found in the number
    Empty,
    Invalid(char, Base),
    NoExponent,
    TooManyDigitsInExponent,
    Overflow,
    FloatOverflow,
    InvalidFloat,
    /// A number was malformed because in contained a dot where it should'nt.
    ///
    /// For example, floating point numbers are not supported in base 16, so
    /// parsing '0x2.1' will trigger this error.
    NumberUnexpectedDot,
}

impl From<ParseFloatError> for NumberError {
    fn from(err: ParseFloatError) -> Self {
        match err {
            ParseFloatError::Empty => Self::Empty,
            ParseFloatError::Invalid => Self::InvalidFloat,
        }
    }
}

impl fmt::Display for NumberError {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Empty => formatter.write_str("empty number"),
            Self::Invalid(c, base) => write!(
                formatter,
                "invalid digit for base {} : '{}'",
                *base as u64, c
            ),
            Self::NoExponent => formatter.write_str("expected number after 'e'"),
            Self::TooManyDigitsInExponent => formatter.write_str("too many digits in exponent"),
            Self::Overflow => formatter.write_str("integer overflow"),
            Self::FloatOverflow => formatter.write_str("float overflow"),
            Self::InvalidFloat => formatter.write_str("Error while parsing float : invalid"),
            Self::NumberUnexpectedDot => write!(formatter, "unexpected dot"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_decompose_decimal_number() {
        assert_eq!(
            decompose_decimal_number(b"013.012").unwrap(),
            Decimal {
                integral: &[b'0', b'1', b'3'],
                fractional: Some(&[b'0', b'1', b'2']),
                exp: 0
            }
        );
        assert_eq!(
            decompose_decimal_number(b"25.5601e-14").unwrap(),
            Decimal {
                integral: &[b'2', b'5'],
                fractional: Some(&[b'5', b'6', b'0', b'1']),
                exp: -14
            }
        );
        assert_eq!(
            decompose_decimal_number(b"_8_4_5e52").unwrap(),
            Decimal {
                integral: &[b'_', b'8', b'_', b'4', b'_', b'5'],
                fractional: Some(&[]),
                exp: 52
            }
        );
        assert_eq!(
            decompose_decimal_number(b"64.").unwrap(),
            Decimal {
                integral: &[b'6', b'4'],
                fractional: Some(&[]),
                exp: 0
            }
        );
        assert_eq!(
            decompose_decimal_number(b".64").unwrap(),
            Decimal {
                integral: &[],
                fractional: Some(&[b'6', b'4']),
                exp: 0
            }
        );
        assert_eq!(
            decompose_decimal_number(b"64").unwrap(),
            Decimal {
                integral: &[b'6', b'4'],
                fractional: None,
                exp: 0
            }
        );

        assert_eq!(
            decompose_decimal_number(b"1.2e").unwrap_err(),
            NumberError::NoExponent
        );
        assert_eq!(
            decompose_decimal_number(b"6e0000000000000000001").unwrap_err(),
            NumberError::TooManyDigitsInExponent
        );
        assert_eq!(
            decompose_decimal_number(b"").unwrap_err(),
            NumberError::Empty
        );
        assert_eq!(
            decompose_decimal_number(b"0f15").unwrap_err(),
            NumberError::Invalid('f', Base::Decimal)
        );
    }

    #[test]
    fn test_decompose_number() {
        assert_eq!(
            decompose_number(b"013.012", Base::Decimal).unwrap(),
            Number {
                integral: &[b'0', b'1', b'3'],
                fractional: Some(&[b'0', b'1', b'2']),
            }
        );
        assert_eq!(
            decompose_number(b"5fa.e4b", Base::Hexadecimal).unwrap(),
            Number {
                integral: &[b'5', b'f', b'a'],
                fractional: Some(&[b'e', b'4', b'b']),
            }
        );
        assert_eq!(
            decompose_number(b"573", Base::Octal).unwrap(),
            Number {
                integral: &[b'5', b'7', b'3'],
                fractional: None,
            }
        );
        assert_eq!(
            decompose_number(b"573.", Base::Octal).unwrap(),
            Number {
                integral: &[b'5', b'7', b'3'],
                fractional: Some(&[]),
            }
        );
        assert_eq!(
            decompose_number(b".573", Base::Octal).unwrap(),
            Number {
                integral: &[],
                fractional: Some(&[b'5', b'7', b'3']),
            }
        );

        assert_eq!(
            decompose_number(b"", Base::Decimal).unwrap_err(),
            NumberError::Empty
        );
        assert_eq!(
            decompose_number(b"hello world !", Base::Decimal).unwrap_err(),
            NumberError::Invalid('h', Base::Decimal)
        );
        assert_eq!(
            decompose_number(b"010012.01001", Base::Binary).unwrap_err(),
            NumberError::Invalid('2', Base::Binary)
        );
    }

    #[test]
    fn the_real_thing() {
        // integers
        assert_eq!(parse_number("65412").unwrap().0, IntOrFloat::Int(65412));
        assert_eq!(parse_number("0x5f2b").unwrap().0, IntOrFloat::Int(24363));
        assert_eq!(parse_number("-0b01101").unwrap().0, IntOrFloat::Int(-13));
        // floats, using rust's parsing functions
        assert_eq!(parse_number("65.412").unwrap().0, IntOrFloat::Float(65.412));
        assert_eq!(
            parse_number("-87.254").unwrap().0,
            IntOrFloat::Float(-87.254)
        );
        // floats, using this crate's functions
        assert_eq!(parse_number("0x12.2").unwrap().0, IntOrFloat::Float(18.125));
        assert_eq!(parse_number("0x22.2").unwrap().0, IntOrFloat::Float(34.125));
        assert_eq!(parse_number("0x32.2").unwrap().0, IntOrFloat::Float(50.125));
        assert_eq!(
            parse_number("0x72.2").unwrap().0,
            IntOrFloat::Float(114.125)
        );
        assert_eq!(
            parse_number("-0x67.241").unwrap().0,
            IntOrFloat::Float(-103.140_869_140_625)
        );

        assert_eq!(
            parse_number("0x12.2").unwrap().0,
            parse_number("0o22.1").unwrap().0
        );
        assert_eq!(
            parse_number("0x12.2").unwrap().0,
            parse_number("0b10010.001").unwrap().0
        );

        assert_eq!(
            parse_number("0x0.5").unwrap().0,
            IntOrFloat::Float(5. / 16.)
        );
        assert_eq!(
            parse_number("0x0.05").unwrap().0,
            IntOrFloat::Float(5. / (16. * 16.))
        );
        assert_eq!(
            parse_number("0o0.64").unwrap().0,
            IntOrFloat::Float(6. / 8. + 4. / (8. * 8.))
        );
        assert_eq!(
            parse_number("0o0.12").unwrap().0,
            IntOrFloat::Float(1. / 8. + 2. / (8. * 8.))
        );
        assert_eq!(
            parse_number("0b000.001001001001").unwrap().0,
            IntOrFloat::Float(1. / 8. + 1. / 64. + 1. / 512. + 1. / 4096.)
        );

        // excessive precision (this is quick !)
        assert_eq!(
            parse_number("0x1.0000000000001").unwrap(),
            (
                IntOrFloat::Float(1.),
                Some(Warning::ExcessiveFloatPrecision)
            )
        );
    }
}

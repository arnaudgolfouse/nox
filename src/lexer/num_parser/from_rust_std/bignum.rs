//! Custom arbitrary-precision number (bignum) implementation.
//!
//! This is designed to avoid the heap allocation at expense of stack memory.
//! The most used bignum type, `Big32x40`, is limited by 32 × 40 = 1,280 bits
//! and will take at most 160 bytes of stack memory. This is more than enough
//! for round-tripping all possible finite `f64` values.
//!
//! In principle it is possible to have multiple bignum types for different
//! inputs, but we don't do so to avoid the code bloat. Each bignum is still
//! tracked for the actual usages, so it normally doesn't matter.

// This module is only for dec2flt and flt2dec, and only public because of coretests.
// It is not intended to ever be stabilized.
#![doc(hidden)]
#![macro_use]

use std::{cmp, fmt, mem};

/// Arithmetic operations required by bignums.
trait FullOps: Sized {
    /// Returns `(carry', v')` such that `carry' * 2^W + v' = self + other + carry`,
    /// where `W` is the number of bits in `Self`.
    fn full_add(self, other: Self, carry: bool) -> (bool /* carry */, Self);

    /// Returns `(carry', v')` such that `carry' * 2^W + v' = self * other + carry`,
    /// where `W` is the number of bits in `Self`.
    fn full_mul(self, other: Self, carry: Self) -> (Self /* carry */, Self);

    /// Returns `(carry', v')` such that `carry' * 2^W + v' = self * other + other2 + carry`,
    /// where `W` is the number of bits in `Self`.
    fn full_mul_add(self, other: Self, other2: Self, carry: Self) -> (Self /* carry */, Self);

    /// Returns `(quo, rem)` such that `borrow * 2^W + self = quo * other + rem`
    /// and `0 <= rem < other`, where `W` is the number of bits in `Self`.
    fn full_div_rem(self, other: Self, borrow: Self)
        -> (Self /* quotient */, Self /* remainder */);
}

impl FullOps for u32 {
    fn full_add(self, other: u32, carry: bool) -> (bool, u32) {
        // This cannot overflow; the output is between `0` and `2 * 2^nbits - 1`.
        // FIXME: will LLVM optimize this into ADC or similar?
        let (v, carry1) = self.overflowing_add(other);
        let (v, carry2) = v.overflowing_add(if carry { 1 } else { 0 });
        (carry1 || carry2, v)
    }

    fn full_mul(self, other: u32, carry: u32) -> (u32, u32) {
        // This cannot overflow;
        // the output is between `0` and `2^nbits * (2^nbits - 1)`.
        // FIXME: will LLVM optimize this into ADC or similar?
        let nbits = mem::size_of::<u32>() * 8;
        let v = (self as u64) * (other as u64) + (carry as u64);
        ((v >> nbits) as u32, v as u32)
    }

    fn full_mul_add(self, other: u32, other2: u32, carry: u32) -> (u32, u32) {
        // This cannot overflow;
        // the output is between `0` and `2^nbits * (2^nbits - 1)`.
        let nbits = mem::size_of::<u32>() * 8;
        let v = (self as u64) * (other as u64) + (other2 as u64) + (carry as u64);
        ((v >> nbits) as u32, v as u32)
    }

    fn full_div_rem(self, other: u32, borrow: u32) -> (u32, u32) {
        debug_assert!(borrow < other);
        // This cannot overflow; the output is between `0` and `other * (2^nbits - 1)`.
        let nbits = mem::size_of::<u32>() * 8;
        let lhs = ((borrow as u64) << nbits) | (self as u64);
        let rhs = other as u64;
        ((lhs / rhs) as u32, (lhs % rhs) as u32)
    }
}

/// Table of powers of 5 representable in digits. Specifically, the largest {u8, u16, u32} value
/// that's a power of five, plus the corresponding exponent. Used in `mul_pow5`.
const SMALL_POW5: [(u64, usize); 3] = [(125, 3), (15625, 6), (1_220_703_125, 13)];

/// The digit type for `Big32x40`.
type Digit32 = u32;

/// Stack-allocated arbitrary-precision (up to certain limit) integer.
///
/// This is backed by a fixed-size array of given type ("digit").
/// While the array is not very large (normally some hundred bytes),
/// copying it recklessly may result in the performance hit.
/// Thus this is intentionally not `Copy`.
///
/// All operations available to bignums panic in the case of overflows.
/// The caller is responsible to use large enough bignum types.
pub(super) struct Big32x40 {
    /// One plus the offset to the maximum "digit" in use.
    /// This does not decrease, so be aware of the computation order.
    /// `base[size..]` should be zero.
    size: usize,
    /// Digits. `[a, b, c, ...]` represents `a + b*2^W + c*2^(2W) + ...`
    /// where `W` is the number of bits in the digit type.
    base: [Digit32; 40],
}

impl Big32x40 {
    /// Makes a bignum from one digit.
    pub(super) fn from_small(v: Digit32) -> Big32x40 {
        let mut base = [0; 40];
        base[0] = v;
        Big32x40 { size: 1, base }
    }

    /// Makes a bignum from `u64` value.
    pub(super) fn from_u64(mut v: u64) -> Big32x40 {
        let mut base = [0; 40];
        let mut sz = 0;
        while v > 0 {
            base[sz] = v as Digit32;
            v >>= mem::size_of::<Digit32>() * 8;
            sz += 1;
        }
        Big32x40 { size: sz, base }
    }

    /// Returns the internal digits as a slice `[a, b, c, ...]` such that the numeric
    /// value is `a + b * 2^W + c * 2^(2W) + ...` where `W` is the number of bits in
    /// the digit type.
    pub(super) fn digits(&self) -> &[Digit32] {
        &self.base[..self.size]
    }

    /// Returns the `i`-th bit where bit 0 is the least significant one.
    /// In other words, the bit with weight `2^i`.
    pub(super) fn get_bit(&self, i: usize) -> u8 {
        let digitbits = mem::size_of::<Digit32>() * 8;
        let d = i / digitbits;
        let b = i % digitbits;
        ((self.base[d] >> b) & 1) as u8
    }

    /// Returns `true` if the bignum is zero.
    pub(super) fn is_zero(&self) -> bool {
        self.digits().iter().all(|&v| v == 0)
    }

    /// Returns the number of bits necessary to represent this value. Note that zero
    /// is considered to need 0 bits.
    pub(super) fn bit_length(&self) -> usize {
        // Skip over the most significant digits which are zero.
        let digits = self.digits();
        let zeros = digits.iter().rev().take_while(|&&x| x == 0).count();
        let end = digits.len() - zeros;
        let nonzero = &digits[..end];

        if nonzero.is_empty() {
            // There are no non-zero digits, i.e., the number is zero.
            return 0;
        }
        // This could be optimized with leading_zeros() and bit shifts, but that's
        // probably not worth the hassle.
        let digitbits = mem::size_of::<Digit32>() * 8;
        let mut i = nonzero.len() * digitbits - 1;
        while self.get_bit(i) == 0 {
            i -= 1;
        }
        i + 1
    }

    pub(super) fn add_small(&mut self, other: Digit32) -> &mut Big32x40 {
        let (mut carry, v) = self.base[0].full_add(other, false);
        self.base[0] = v;
        let mut i = 1;
        while carry {
            let (c, v) = self.base[i].full_add(0, carry);
            self.base[i] = v;
            carry = c;
            i += 1;
        }
        if i > self.size {
            self.size = i;
        }
        self
    }

    /// Subtracts `other` from itself and returns its own mutable reference.
    pub(super) fn sub<'a>(&'a mut self, other: &Big32x40) -> &'a mut Big32x40 {
        let sz = cmp::max(self.size, other.size);
        let mut noborrow = true;
        for (a, b) in self.base[..sz].iter_mut().zip(&other.base[..sz]) {
            let (c, v) = (*a).full_add(!*b, noborrow);
            *a = v;
            noborrow = c;
        }
        debug_assert!(noborrow);
        self.size = sz;
        self
    }

    /// Multiplies itself by a digit-sized `other` and returns its own
    /// mutable reference.
    pub(super) fn mul_small(&mut self, other: Digit32) -> &mut Big32x40 {
        let mut sz = self.size;
        let mut carry = 0;
        for a in &mut self.base[..sz] {
            let (c, v) = (*a).full_mul(other, carry);
            *a = v;
            carry = c;
        }
        if carry > 0 {
            self.base[sz] = carry;
            sz += 1;
        }
        self.size = sz;
        self
    }

    /// Multiplies itself by `2^bits` and returns its own mutable reference.
    pub(super) fn mul_pow2(&mut self, bits: usize) -> &mut Big32x40 {
        let digitbits = mem::size_of::<Digit32>() * 8;
        let digits = bits / digitbits;
        let bits = bits % digitbits;

        debug_assert!(digits < 40);
        debug_assert!(self.base[40 - digits..].iter().all(|&v| v == 0));
        debug_assert!(bits == 0 || (self.base[40 - digits - 1] >> (digitbits - bits)) == 0);

        // shift by `digits * digitbits` bits
        for i in (0..self.size).rev() {
            self.base[i + digits] = self.base[i];
        }
        for i in 0..digits {
            self.base[i] = 0;
        }

        // shift by `bits` bits
        let mut sz = self.size + digits;
        if bits > 0 {
            let last = sz;
            let overflow = self.base[last - 1] >> (digitbits - bits);
            if overflow > 0 {
                self.base[last] = overflow;
                sz += 1;
            }
            for i in (digits + 1..last).rev() {
                self.base[i] = (self.base[i] << bits) | (self.base[i - 1] >> (digitbits - bits));
            }
            self.base[digits] <<= bits;
            // self.base[..digits] is zero, no need to shift
        }

        self.size = sz;
        self
    }

    /// Multiplies itself by `5^e` and returns its own mutable reference.
    pub(super) fn mul_pow5(&mut self, mut e: usize) -> &mut Big32x40 {
        // There are exactly n trailing zeros on 2^n, and the only relevant digit sizes
        // are consecutive powers of two, so this is well suited index for the table.
        let table_index = mem::size_of::<Digit32>().trailing_zeros() as usize;
        let (small_power, small_e) = SMALL_POW5[table_index];
        let small_power = small_power as Digit32;

        // Multiply with the largest single-digit power as long as possible ...
        while e >= small_e {
            self.mul_small(small_power);
            e -= small_e;
        }

        // ... then finish off the remainder.
        let mut rest_power = 1;
        for _ in 0..e {
            rest_power *= 5;
        }
        self.mul_small(rest_power);

        self
    }

    /// Multiplies itself by a number described by `other[0] + other[1] * 2^W +
    /// other[2] * 2^(2W) + ...` (where `W` is the number of bits in the digit type)
    /// and returns its own mutable reference.
    pub(super) fn mul_digits<'a>(&'a mut self, other: &[Digit32]) -> &'a mut Big32x40 {
        // the internal routine. works best when aa.len() <= bb.len().
        fn mul_inner(ret: &mut [Digit32; 40], aa: &[Digit32], bb: &[Digit32]) -> usize {
            let mut retsz = 0;
            for (i, &a) in aa.iter().enumerate() {
                if a == 0 {
                    continue;
                }
                let mut sz = bb.len();
                let mut carry = 0;
                for (j, &b) in bb.iter().enumerate() {
                    let (c, v) = a.full_mul_add(b, ret[i + j], carry);
                    ret[i + j] = v;
                    carry = c;
                }
                if carry > 0 {
                    ret[i + sz] = carry;
                    sz += 1;
                }
                if retsz < i + sz {
                    retsz = i + sz;
                }
            }
            retsz
        }

        let mut ret = [0; 40];
        let retsz = if self.size < other.len() {
            mul_inner(&mut ret, &self.digits(), other)
        } else {
            mul_inner(&mut ret, other, &self.digits())
        };
        self.base = ret;
        self.size = retsz;
        self
    }

    /// Divide self by another bignum, overwriting `q` with the quotient and `r` with the
    /// remainder.
    pub(super) fn div_rem(&self, d: &Big32x40, q: &mut Big32x40, r: &mut Big32x40) {
        // Stupid slow base-2 long division taken from
        // https://en.wikipedia.org/wiki/Division_algorithm
        // FIXME use a greater base (Digit32) for the long division.
        debug_assert!(!d.is_zero());
        let digitbits = mem::size_of::<Digit32>() * 8;
        for digit in &mut q.base[..] {
            *digit = 0;
        }
        for digit in &mut r.base[..] {
            *digit = 0;
        }
        r.size = d.size;
        q.size = 1;
        let mut q_is_zero = true;
        let end = self.bit_length();
        for i in (0..end).rev() {
            r.mul_pow2(1);
            r.base[0] |= self.get_bit(i) as Digit32;
            if &*r >= d {
                r.sub(d);
                // Set bit `i` of q to 1.
                let digit_idx = i / digitbits;
                let bit_idx = i % digitbits;
                if q_is_zero {
                    q.size = digit_idx + 1;
                    q_is_zero = false;
                }
                q.base[digit_idx] |= 1 << bit_idx;
            }
        }
        debug_assert!(q.base[q.size..].iter().all(|&d| d == 0));
        debug_assert!(r.base[r.size..].iter().all(|&d| d == 0));
    }
}

impl cmp::PartialEq for Big32x40 {
    fn eq(&self, other: &Big32x40) -> bool {
        self.base[..] == other.base[..]
    }
}

impl cmp::Eq for Big32x40 {}

impl cmp::PartialOrd for Big32x40 {
    fn partial_cmp(&self, other: &Big32x40) -> std::option::Option<cmp::Ordering> {
        std::option::Option::Some(self.cmp(other))
    }
}

impl cmp::Ord for Big32x40 {
    fn cmp(&self, other: &Big32x40) -> cmp::Ordering {
        use cmp::max;
        let sz = max(self.size, other.size);
        let lhs = self.base[..sz].iter().cloned().rev();
        let rhs = other.base[..sz].iter().cloned().rev();
        lhs.cmp(rhs)
    }
}

impl std::clone::Clone for Big32x40 {
    fn clone(&self) -> Self {
        Self {
            size: self.size,
            base: self.base,
        }
    }
}

impl fmt::Debug for Big32x40 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let sz = if self.size < 1 { 1 } else { self.size };
        let digitlen = mem::size_of::<Digit32>() * 2;

        write!(f, "{:#x}", self.base[sz - 1])?;
        for &v in self.base[..sz - 1].iter().rev() {
            write!(f, "_{:01$x}", v, digitlen)?;
        }
        std::result::Result::Ok(())
    }
}

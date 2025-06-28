//! Special 24-bit unsigned integers implementation.

use core::fmt;

use crate::error;

#[allow(non_camel_case_types)]
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
/// Make a distinct type for `u24`.
///
/// This type is little-endian and uses 3 bytes to represent a number.
pub struct u24([u8; 3]);

impl fmt::Debug for u24 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{}", self.to_u32()))
    }
}

impl u24 {
    /// BITS value for `u24`, which is `24`.
    pub const BITS: u32 = 24;
    /// MAX value for `u24`, which is `0x00FF_FFFF`.
    pub const MAX: Self = Self([0xFF, 0xFF, 0xFF]);
    /// MIN value for `u24`, which is `0x0000_0000`.
    pub const MIN: Self = Self([0x00, 0x00, 0x00]);

    #[inline]
    /// Converts the [`u24`] to a [`u32`] losslessly, as [`u24`] is guaranteed
    /// to fit in a [`u32`].
    pub const fn to_u32(self) -> u32 {
        let u24([a, b, c]) = self;

        u32::from_le_bytes([a, b, c, 0])
    }

    #[inline]
    /// Converts the [`u24`] to a [`usize`] losslessly, as [`u24`] is guaranteed
    /// to fit in a [`usize`].
    pub const fn to_usize(self) -> usize {
        self.to_u32() as usize
    }

    #[inline]
    /// Converts a [`u8`] to a [`u24`] losslessly.
    pub const fn from_u8(n: u8) -> Self {
        u24([n, 0, 0])
    }

    #[inline]
    /// Converts a [`u8`] to a [`u24`] losslessly.
    pub const fn from_u8_unchecked(n: u8) -> Self {
        u24([n, 0, 0])
    }

    #[inline]
    /// Converts a [`u16`] to a [`u24`] losslessly.
    pub const fn from_u16(n: u16) -> Self {
        let [a, b] = n.to_le_bytes();

        u24([a, b, 0])
    }

    #[inline]
    /// Converts a [`u16`] to a [`u24`] losslessly.
    pub const fn from_u16_unchecked(n: u16) -> Self {
        let [a, b] = n.to_le_bytes();

        u24([a, b, 0])
    }

    #[inline]
    #[cfg_attr(feature = "feat-const", rustversion::attr(since(1.83.0), const))]

    /// Converts a [`u32`] to a [`u24`], but asserts that will not overflow.
    ///
    /// # Const context
    ///
    /// This function can be used in a const context since Rust 1.83.0. You
    /// should enable the feature `feat-const` first (default enabled).
    pub fn from_u32(n: u32) -> Self {
        Self::try_from_u32(n).expect("u32 value is too large for u24")
    }

    #[inline]
    /// Converts a [`u32`] to a [`u24`], but cuts off the upper bits.
    pub const fn from_u32_unchecked(n: u32) -> Self {
        let [a, b, c, _] = n.to_le_bytes();

        u24([a, b, c])
    }

    #[inline]
    /// Try converts a [`u32`] to a [`u24`], return `None` if the [`u32`] is too
    /// large.
    pub const fn try_from_u32(n: u32) -> Option<Self> {
        let [a, b, c, 0] = n.to_le_bytes() else {
            return None;
        };

        Some(u24([a, b, c]))
    }

    #[inline]
    #[cfg_attr(feature = "feat-const", rustversion::attr(since(1.83.0), const))]
    /// Converts a [`usize`] to a [`u24`], but asserts that will not overflow.
    ///
    /// # Const context
    ///
    /// This function can be used in a const context since Rust 1.83.0. You
    /// should enable the feature `feat-const` first (default enabled).
    pub fn from_usize(n: usize) -> Self {
        Self::try_from_usize(n).expect("usize value is too large for u24")
    }

    #[inline]
    /// Converts a [`usize`] to a [`u24`], but cuts off the upper bits.
    pub const fn from_usize_unchecked(n: usize) -> Self {
        let [a, b, c, ..] = n.to_le_bytes();

        u24([a, b, c])
    }

    #[inline]
    /// Try converts a [`usize`] to a [`u24`], return `None` if the [`usize`] is
    /// too large.
    pub const fn try_from_usize(n: usize) -> Option<Self> {
        if n > Self::MAX.to_u32() as usize {
            return None;
        }

        let [a, b, c, ..] = n.to_le_bytes();

        Some(u24([a, b, c]))
    }

    #[inline]
    /// Adds two [`u24`] values, returning `None` if the result would overflow.
    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        self.checked_add_u32(rhs.to_u32())
    }

    #[inline]
    /// Adds [`u32`] to [`u24`] values, returning `None` if the result would
    /// overflow.
    pub const fn checked_add_u32(self, rhs: u32) -> Option<Self> {
        let Some(sum) = self.to_u32().checked_add(rhs) else {
            return None;
        };

        Self::try_from_u32(sum)
    }

    #[inline]
    /// Adds [`usize`] to [`u24`] values, returning `None` if the result would
    /// overflow.
    pub const fn checked_add_usize(self, rhs: usize) -> Option<Self> {
        let Some(sum) = self.to_usize().checked_add(rhs) else {
            return None;
        };

        Self::try_from_usize(sum)
    }

    #[inline]
    /// Subtracts two [`u24`] values, returning `None` if the result would be
    /// negative.
    pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.checked_sub_u32(rhs.to_u32())
    }

    #[inline]
    /// Subtracts [`u32`] from [`u24`] values, returning `None` if the result
    /// would be negative.
    pub const fn checked_sub_u32(self, rhs: u32) -> Option<Self> {
        let Some(diff) = self.to_u32().checked_sub(rhs) else {
            return None;
        };

        Self::try_from_u32(diff)
    }

    #[inline]
    /// Subtracts [`usize`] from [`u24`] values, returning `None` if the result
    /// would be negative.
    pub const fn checked_sub_usize(self, rhs: usize) -> Option<Self> {
        let Some(diff) = self.to_usize().checked_sub(rhs) else {
            return None;
        };

        Self::try_from_usize(diff)
    }

    #[inline]
    /// Converts the `u24` from a big-endian byte array.
    pub const fn from_be_bytes(bytes: [u8; 3]) -> Self {
        let [a, b, c] = bytes;

        Self([c, b, a])
    }

    #[inline]
    /// Converts the `u24` to a big-endian byte array.
    pub const fn to_be_bytes(self) -> [u8; 3] {
        let Self([a, b, c]) = self;

        [c, b, a]
    }

    #[inline]
    /// Converts the `u24` from a little-endian byte array.
    pub const fn from_le_bytes(bytes: [u8; 3]) -> Self {
        Self(bytes)
    }

    #[inline]
    /// Converts the `u24` to a little-endian byte array.
    pub const fn to_le_bytes(self) -> [u8; 3] {
        self.0
    }
}

impl From<u16> for u24 {
    fn from(value: u16) -> Self {
        u24::from_u16(value)
    }
}

impl TryFrom<u32> for u24 {
    type Error = error::InvalidLength;

    #[inline]
    fn try_from(value: u32) -> Result<Self, Self::Error> {
        u24::try_from_u32(value).ok_or(error::InvalidLength)
    }
}

impl TryFrom<usize> for u24 {
    type Error = error::InvalidLength;

    #[inline]
    fn try_from(value: usize) -> Result<Self, Self::Error> {
        u24::try_from_usize(value).ok_or(error::InvalidLength)
    }
}

#[cfg(test)]
mod tests {
    use std::format;

    use super::*;

    #[test]
    fn test_constants() {
        // 测试常量值
        assert_eq!(u24::MAX.to_u32(), 0x00FF_FFFF);
        assert_eq!(u24::MIN.to_u32(), 0);
    }

    #[test]
    fn test_to_u32() {
        // Basic conversion
        let val = u24([0x34, 0x12, 0x00]);
        assert_eq!(val.to_u32(), 0x0012_34);

        // Maximum value
        let max_val = u24([0xFF, 0xFF, 0xFF]);
        assert_eq!(max_val.to_u32(), 0x00FF_FFFF);

        // Minimum value
        let min_val = u24([0x00, 0x00, 0x00]);
        assert_eq!(min_val.to_u32(), 0);
    }

    #[test]
    fn test_from_u32() {
        // Basic conversion
        let val = u24::from_u32(0x123456);
        assert_eq!(val.to_u32(), 0x123456);

        // Boundary values
        let max_val = u24::from_u32(0x00FF_FFFF);
        assert_eq!(max_val.to_u32(), 0x00FF_FFFF);
        let min_val = u24::from_u32(0);
        assert_eq!(min_val.to_u32(), 0);
    }

    #[test]
    #[should_panic(expected = "u32 value is too large for u24")]
    fn test_from_u32_overflow() {
        u24::from_u32(0x0100_0000);
    }

    #[test]
    #[should_panic(expected = "u32 value is too large for u24")]
    fn test_from_u32_max_overflow() {
        u24::from_u32(u32::MAX);
    }

    #[test]
    fn test_try_from_u32() {
        assert_eq!(u24::try_from_u32(0x123456).unwrap().to_u32(), 0x123456);
        assert_eq!(
            u24::try_from_u32(0x00FF_FFFF).unwrap().to_u32(),
            0x00FF_FFFF
        );
        assert_eq!(u24::try_from_u32(0).unwrap().to_u32(), 0);

        assert!(u24::try_from_u32(0x0100_0000).is_none());
        assert!(u24::try_from_u32(u32::MAX).is_none());
        assert!(u24::try_from_u32(0x01FF_FFFF).is_none());
    }

    #[test]
    fn test_from_u32_unchecked() {
        let val = u24::from_u32_unchecked(0x123456);
        assert_eq!(val.to_u32(), 0x123456);

        let max_val = u24::from_u32_unchecked(0x00FF_FFFF);
        assert_eq!(max_val.to_u32(), 0x00FF_FFFF);
    }

    #[test]
    fn test_checked_add() {
        let a = u24::from_u32(0x0010_0000);
        let b = u24::from_u32(0x0020_0000);

        // Simple
        assert_eq!(
            a.checked_add(b).unwrap().to_u32(),
            0x0010_0000 + 0x0020_0000
        );

        // Overflow
        let max = u24::MAX;
        let one = u24::from_u32(1);
        assert!(max.checked_add(one).is_none());

        // Boundary case
        let almost_max = u24::from_u32(0x00FF_FFFE);
        assert_eq!(almost_max.checked_add(one).unwrap().to_u32(), 0x00FF_FFFF);
        assert!(almost_max
            .checked_add(one)
            .unwrap()
            .checked_add(one)
            .is_none());
    }

    #[test]
    fn test_checked_add_u32() {
        let a = u24::from_u32(0x0010_0000);

        // Simple
        assert_eq!(
            a.checked_add_u32(0x0020_0000).unwrap().to_u32(),
            0x0010_0000 + 0x0020_0000
        );

        // Overflow
        let max = u24::MAX;
        assert!(max.checked_add_u32(1).is_none());
        assert!(a.checked_add_u32(0x00F0_0000).is_none());

        // Boundary case
        let almost_max = u24::from_u32(0x00FF_FFFE);
        assert_eq!(almost_max.checked_add_u32(1).unwrap().to_u32(), 0x00FF_FFFF);
        assert!(almost_max.checked_add_u32(2).is_none());
    }

    #[test]
    fn test_checked_sub() {
        let a = u24::from_u32(0x0010_0000 + 0x0020_0000);
        let b = u24::from_u32(0x0010_0000);

        assert_eq!(a.checked_sub(b).unwrap().to_u32(), 0x0020_0000);
        assert!(a
            .checked_sub(u24::from_u32(0x0010_0000 + 0x0020_0000 + 1))
            .is_none());

        let min = u24::MIN;
        assert!(min.checked_sub(u24::from_u32(1)).is_none());

        assert_eq!(a.checked_sub(a).unwrap().to_u32(), 0);
    }

    #[test]
    fn test_checked_sub_u32() {
        let a = u24::from_u32(0x0010_0000 + 0x0020_0000);

        assert_eq!(
            a.checked_sub_u32(0x0010_0000).unwrap().to_u32(),
            0x0020_0000
        );

        assert!(a.checked_sub_u32(0x0010_0000 + 0x0020_0000 + 1).is_none());

        let min = u24::MIN;
        assert!(min.checked_sub_u32(1).is_none());

        assert_eq!(a.checked_sub_u32(a.to_u32()).unwrap().to_u32(), 0);
    }

    #[test]
    fn test_byte_conversions() {
        let test_value = 0x00_12_34_56;
        let u24_val = u24::from_u32(test_value);

        let le_bytes = u24_val.to_le_bytes();
        assert_eq!(le_bytes, test_value.to_le_bytes()[..3]);

        let from_le = u24::from_le_bytes([0x56, 0x34, 0x12]);
        assert_eq!(from_le.to_u32(), test_value);

        let be_bytes = u24_val.to_be_bytes();
        assert_eq!(be_bytes, test_value.to_be_bytes()[1..]);

        let from_be = u24::from_be_bytes([0x12, 0x34, 0x56]);
        assert_eq!(from_be.to_u32(), test_value);
    }

    #[test]
    fn test_byte_conversions_edge_cases() {
        let max_val = u24::MAX;
        let max_le_bytes = max_val.to_le_bytes();
        assert_eq!(max_le_bytes, [0xFF, 0xFF, 0xFF]);
        assert_eq!(u24::from_le_bytes(max_le_bytes).to_u32(), 0x00FF_FFFF);

        let max_be_bytes = max_val.to_be_bytes();
        assert_eq!(max_be_bytes, [0xFF, 0xFF, 0xFF]);
        assert_eq!(u24::from_be_bytes(max_be_bytes).to_u32(), 0x00FF_FFFF);

        let min_val = u24::MIN;
        let min_le_bytes = min_val.to_le_bytes();
        assert_eq!(min_le_bytes, [0x00, 0x00, 0x00]);
        assert_eq!(u24::from_le_bytes(min_le_bytes).to_u32(), 0);

        let min_be_bytes = min_val.to_be_bytes();
        assert_eq!(min_be_bytes, [0x00, 0x00, 0x00]);
        assert_eq!(u24::from_be_bytes(min_be_bytes).to_u32(), 0);
    }

    #[test]
    fn test_debug_format() {
        let val = u24::from_u32(0x123456);
        let debug_str = std::format!("{:?}", val);
        assert_eq!(debug_str, "1193046"); // 0x123456 in decimal

        let max_val = u24::MAX;
        let max_debug_str = format!("{:?}", max_val);
        assert_eq!(max_debug_str, "16777215"); // 0x00FFFFFF in decimal
    }

    #[test]
    fn test_endianness_consistency() {
        // 测试大小端序转换的一致性
        for value in [0u32, 1, 0x123456, 0x00FF_FFFF] {
            let u24_val = u24::from_u32(value);

            let le_bytes = u24_val.to_le_bytes();
            let from_le = u24::from_le_bytes(le_bytes);
            assert_eq!(from_le.to_u32(), value);

            let be_bytes = u24_val.to_be_bytes();
            let from_be = u24::from_be_bytes(be_bytes);
            assert_eq!(from_be.to_u32(), value);
        }
    }

    #[test]
    fn test_arithmetic_edge_cases() {
        let zero = u24::MIN;
        let max = u24::MAX;

        // 0 + 0 = 0
        assert_eq!(zero.checked_add(zero).unwrap().to_u32(), 0);

        // max + 0 = max
        assert_eq!(max.checked_add(zero).unwrap().to_u32(), 0x00FF_FFFF);

        // max - max = 0
        assert_eq!(max.checked_sub(max).unwrap().to_u32(), 0);

        // 0 - 0 = 0
        assert_eq!(zero.checked_sub(zero).unwrap().to_u32(), 0);
    }
}

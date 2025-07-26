//! Error types.

use core::num::NonZeroUsize;

#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
#[derive(thiserror::Error)]
#[error("Insufficient data, need {remaining_bytes} bytes to complete the operation.")]
/// Error: insufficient data.
pub struct InsufficientData {
    pub remaining_bytes: NonZeroUsize,
}

impl InsufficientData {
    #[inline]
    /// Create a new `InsufficientData` error with the given remaining bytes.
    pub const fn check(required_len: usize, actual_len: usize) -> Result<(), Self> {
        match required_len.checked_sub(actual_len) {
            Some(remaining) => match NonZeroUsize::new(remaining) {
                Some(remaining_bytes) => Err(Self { remaining_bytes }),
                None => Ok(()), // No remaining bytes, so no error
            },
            _ => Ok(()),
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[derive(thiserror::Error)]
#[error("Trailing data found after reading the expected length.")]
/// Error: trailing data.
pub struct TrailingData;

#[derive(Debug, Clone, Copy)]
#[derive(thiserror::Error)]
#[error("Invalid length when parsing type")]
/// Error: invalid length.
pub struct InvalidLength;

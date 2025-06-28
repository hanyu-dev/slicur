//! Error types.

#[derive(Debug, Clone, Copy)]
#[derive(thiserror::Error)]
#[error("Insufficient data, need more bytes to complete the operation.")]
/// Error: insufficient data.
pub struct InsufficientData;

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

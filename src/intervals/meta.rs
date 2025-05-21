//! Interval metadata
//!
//! Information about relativity, openness, opening direction, etc.

/// How open is the time interval
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Openness {
    /// Defined start and end bounds
    Closed,
    /// One of the bounds is known, but the interval continues to infinity in one direction
    HalfOpen,
    /// Covers the entire time
    Open,
}

/// Whether the time interval is bound to specific timestamps
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Relativity {
    Relative,
    Absolute,
}

/// The direction in which a half-open time interval is open
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum OpeningDirection {
    ToFuture,
    ToPast,
}

/// Time interval duration
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Duration {
    Finite(chrono::Duration),
    Infinite,
}

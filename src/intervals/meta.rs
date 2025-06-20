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
    /// Is technically bounded in time, but nowhere precise, used for [empty intervals](super::interval::EmptyInterval)
    Empty,
}

/// Trait for any interval representation that supports the concept of [`Openness`]
pub trait HasOpenness {
    fn openness(&self) -> Openness;
}

/// Whether the time interval is bound to specific timestamps
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Relativity {
    /// Bounds are set using offsets
    Relative,
    /// Bounds are set using specific timestamps
    Absolute,
    /// Uses concepts rather than bounds, like [open](super::interval::OpenInterval)
    /// and [empty](super::interval::EmptyInterval) intervals
    Any,
}

/// Trait for any interval representation that supports the concept of [`Relativity`]
pub trait HasRelativity {
    fn relativity(&self) -> Relativity;
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

/// Trait for any interval representation that supports the concept of [`Duration`]
pub trait HasDuration {
    fn duration(&self) -> Duration;
}

/// Inclusivity of an interval's time bound
///
/// Inclusive by default, exclusive meaning that the given bound time shouldn't count.
/// For example, if two intervals "touch" but one of them has an exclusive bound on this point, then
/// they are counted as not overlapping.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub enum BoundInclusivity {
    #[default]
    Inclusive,
    Exclusive,
}

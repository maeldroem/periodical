//! Interval metadata
//!
//! Information about relativity, openness, opening direction, etc.

use std::fmt::Display;

/// How open is the time interval
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl Display for Openness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Closed => write!(f, "Closed"),
            Self::HalfOpen => write!(f, "Half-open"),
            Self::Open => write!(f, "Open"),
            Self::Empty => write!(f, "Empty"),
        }
    }
}

/// Trait for any interval representation that supports the concept of [`Openness`]
pub trait HasOpenness {
    fn openness(&self) -> Openness;
}

/// Whether the time interval is bound to specific timestamps
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Relativity {
    /// Bounds are set using offsets
    Relative,
    /// Bounds are set using specific timestamps
    Absolute,
    /// Uses concepts rather than bounds, like [open](super::interval::OpenInterval)
    /// and [empty](super::interval::EmptyInterval) intervals
    Any,
}

impl Display for Relativity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Relative => write!(f, "Relative"),
            Self::Absolute => write!(f, "Absolute"),
            Self::Any => write!(f, "Any relativity"),
        }
    }
}

/// Trait for any interval representation that supports the concept of [`Relativity`]
pub trait HasRelativity {
    fn relativity(&self) -> Relativity;
}

/// The direction in which a half-open time interval is open
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpeningDirection {
    ToFuture,
    ToPast,
}

impl Display for OpeningDirection {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ToFuture => write!(f, "Opening direction towards future"),
            Self::ToPast => write!(f, "Opening direction towards past"),
        }
    }
}

/// Time interval duration
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Duration {
    Finite(chrono::Duration),
    Infinite,
}

impl Display for Duration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Finite(duration) => write!(f, "Finite duration: {duration}"),
            Self::Infinite => write!(f, "Infinite duration"),
        }
    }
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
pub enum BoundInclusivity {
    #[default]
    Inclusive,
    Exclusive,
}

impl BoundInclusivity {
    /// Returns the opposite bound inclusivity
    #[must_use]
    pub fn opposite(&self) -> BoundInclusivity {
        match self {
            BoundInclusivity::Inclusive => BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive => BoundInclusivity::Inclusive,
        }
    }
}

impl Display for BoundInclusivity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Inclusive => write!(f, "Inclusive bound"),
            Self::Exclusive => write!(f, "Exclusive bound"),
        }
    }
}

/// Trait for returning the inclusivity of a bound
pub trait HasBoundInclusivity {
    /// Returns the bound inclusivity of the bound
    #[must_use]
    fn inclusivity(&self) -> BoundInclusivity;
}

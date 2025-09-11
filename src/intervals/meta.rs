//! Interval metadata
//!
//! Contains information about intervals such as [`Relativity`], [`Openness`], [`OpeningDirection`], and more.

use std::fmt::Display;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;

/// Global interval trait
///
/// All intervals implement this trait.
///
/// This trait is used for restricting parameters to intervals when the parameter itself is not important, but want
/// to avoid implementing the method on non-interval types.
///
/// For example, extending an [`UnboundedInterval`](crate::intervals::special::UnboundedInterval)
/// with any other interval will produce an [`UnboundedInterval`](crate::intervals::special::UnboundedInterval)
/// anyways, but we don't want to allow calls like `unbounded_interval.extend(3)`,
/// so this trait is used to restrict this parameter to interval types only.
pub trait Interval {}

/// Interval openness
///
/// Describes how open is the interval is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum Openness {
    /// Defined start and end bounds
    Bounded,
    /// One of the bounds is known, but the interval continues to infinity in one direction
    HalfBounded,
    /// Covers the entire time
    Unbounded,
    /// Is technically bounded to time, but nowhere precise.
    ///
    /// Used for [`EmptyInterval`](crate::intervals::special::EmptyInterval)
    Empty,
}

impl Display for Openness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bounded => write!(f, "Bounded"),
            Self::HalfBounded => write!(f, "Half-bounded"),
            Self::Unbounded => write!(f, "Unbounded"),
            Self::Empty => write!(f, "Empty"),
        }
    }
}

/// Possession of [`Openness`]
///
/// This trait should be implemented by all intervals supporting the concept of [`Openness`].
pub trait HasOpenness {
    /// Returns the [`Openness`] of the interval
    #[must_use]
    fn openness(&self) -> Openness;
}

/// Interval relativity
///
/// An interval relativity defines in which kind of time it lives in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum Relativity {
    /// Interval lives in absolute time
    ///
    /// This means that it uses [`DateTime`](chrono::DateTime)s, which are technically relative
    /// on the [Unix epoch](https://en.wikipedia.org/w/index.php?title=Unix_time&oldid=1308795653) but that
    /// we qualify as _absolute time_.
    Absolute,
    /// Interval lives in relative time
    ///
    /// This means that it uses [`Duration`](chrono::Duration)s, also known as offsets.
    ///
    /// For example, if you compare and absolute interval to a point in time, e.g. this day compared to this year's
    /// 1st of January at midnight, you will end up with a relative interval.
    Relative,
    /// Interval isn't bound to relativity
    ///
    /// This means the interval uses a concept rather than representing itself through a time frame.
    ///
    /// It is used by intervals such as [`UnboundedInterval`](crate::intervals::special::UnboundedInterval)
    /// and [`EmptyInterval`](crate::intervals::special::EmptyInterval).
    ///
    /// The variant is called "Any" as those special intervals can be interpreted in both absolute and relative
    /// time frames.
    Any,
}

impl Display for Relativity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Absolute => write!(f, "Absolute"),
            Self::Relative => write!(f, "Relative"),
            Self::Any => write!(f, "Any relativity"),
        }
    }
}

/// Possession of [`Relativity`]
///
/// This trait should be implemented by all interval supporting the concept of [`Relativity`].
pub trait HasRelativity {
    /// Returns the [`Relativity`] of the interval
    #[must_use]
    fn relativity(&self) -> Relativity;
}

/// Opening direction of half-bounded intervals
///
/// This indicates which _direction_ the half-bounded interval covers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum OpeningDirection {
    /// Infinitely towards future
    ToFuture,
    /// Infinitely towards past
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

/// Converts a [`bool`] into an [`OpeningDirection`]
///
/// The boolean is interpreted as _is it going to future?_
impl From<bool> for OpeningDirection {
    fn from(goes_to_future: bool) -> Self {
        if goes_to_future {
            OpeningDirection::ToFuture
        } else {
            OpeningDirection::ToPast
        }
    }
}

/// Interval duration
///
/// Supports `chrono`'s [`Duration`](chrono::Duration) for finite durations and supports
/// representation for infinite durations.
///
/// In the future this enumerator will contain more variants to account for infinitesimal durations
/// (also known as _epsilon_) differences created by the use of [exclusive bounds](BoundInclusivity::Exclusive).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum Duration {
    /// Finite duration
    Finite(chrono::Duration),
    /// Infinite duration
    Infinite,
}

impl Duration {
    /// Returns whether the interval duration is finite
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::Duration;
    /// assert!(Duration::Finite(chrono::Duration::hours(1)).is_finite());
    /// ```
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Duration::Finite(_))
    }

    /// Returns the content of the [`Finite`](Duration::Finite) variant
    ///
    /// Consumes `self` and puts the content of the [`Finite`](Duration::Finite) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    #[must_use]
    pub fn finite(self) -> Option<chrono::Duration> {
        match self {
            Self::Finite(duration) => Some(duration),
            Self::Infinite => None,
        }
    }
}

impl Display for Duration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Finite(duration) => write!(f, "Finite duration: {duration}"),
            Self::Infinite => write!(f, "Infinite duration"),
        }
    }
}

impl From<chrono::Duration> for Duration {
    fn from(duration: chrono::Duration) -> Self {
        Duration::Finite(duration)
    }
}

/// Possession of [`Duration`]
///
/// This trait should be implements by all intervals supporting the concept of [`Duration`].
pub trait HasDuration {
    /// Returns the [`Duration`] of the interval
    fn duration(&self) -> Duration;
}

/// Inclusivity of an interval's bound
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
pub enum BoundInclusivity {
    /// Includes the point described by the bound
    #[default]
    Inclusive,
    /// Excludes the point described by the bound
    ///
    /// An exclusive bound inclusivity means that virtually anything except the described point given by the bound
    /// is included.
    /// Of course, in the context of an interval it also possesses a dimension of _direction_.
    ///
    /// Learn more about the directionality of bound inclusivity
    /// in the [documentation of the `intervals` module](crate::intervals).
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

/// Converts a [`bool`] into a [`BoundInclusivity`]
///
/// The boolean is interpreted as _is it inclusive?_
impl From<bool> for BoundInclusivity {
    fn from(is_inclusive: bool) -> Self {
        if is_inclusive {
            BoundInclusivity::Inclusive
        } else {
            BoundInclusivity::Exclusive
        }
    }
}

/// Possession of [`BoundInclusivity`]
///
/// This trait should be implemented by all interval bounds supporting the concept of [`BoundInclusivity`].
pub trait HasBoundInclusivity {
    /// Returns the [`BoundInclusivity`] of the bound
    #[must_use]
    fn inclusivity(&self) -> BoundInclusivity;
}

/// Capacity of an interval to be empty
pub trait Emptiable {
    /// Returns whether the interval is empty
    fn is_empty(&self) -> bool;
}

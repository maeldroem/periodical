//! Interval metadata
//!
//! Contains information about intervals such as [`Relativity`], [`Openness`], [`OpeningDirection`], and more.

use std::error::Error;
use std::fmt::Display;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

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
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
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
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
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
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
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

/// Infinitesimal duration variation of an interval
///
/// Represents the infinitesimal duration variation(s) created by [exclusive bounds](BoundInclusivity::Exclusive).
///
/// An infinitesimal duration is represented by an epsilon sign, hence the name.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum Epsilon {
    /// No epsilon
    #[default]
    None,
    /// Epsilon variation on start bound
    Start,
    /// Epsilon variation on end bound
    End,
    /// Epsilon variation on both bounds
    Both,
}

impl Epsilon {
    /// Returns whether an epsilon is present
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::Epsilon;
    /// assert!(Epsilon::Start.has_epsilon());
    /// assert!(Epsilon::End.has_epsilon());
    /// assert!(Epsilon::Both.has_epsilon());
    /// assert!(!Epsilon::None.has_epsilon());
    /// ```
    #[must_use]
    pub fn has_epsilon(&self) -> bool {
        !matches!(self, Self::None)
    }

    /// Returns whether the start bound has an epsilon
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::Epsilon;
    /// assert!(Epsilon::Start.has_epsilon_on_start());
    /// assert!(Epsilon::Both.has_epsilon_on_start());
    /// assert!(!Epsilon::None.has_epsilon_on_start());
    /// assert!(!Epsilon::End.has_epsilon_on_start());
    /// ```
    #[must_use]
    pub fn has_epsilon_on_start(&self) -> bool {
        matches!(self, Self::Start | Self::Both)
    }

    /// Returns whether the end bound has an epsilon
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::Epsilon;
    /// assert!(Epsilon::End.has_epsilon_on_end());
    /// assert!(Epsilon::Both.has_epsilon_on_end());
    /// assert!(!Epsilon::None.has_epsilon_on_end());
    /// assert!(!Epsilon::Start.has_epsilon_on_end());
    /// ```
    #[must_use]
    pub fn has_epsilon_on_end(&self) -> bool {
        matches!(self, Self::End | Self::Both)
    }

    /// Interprets the epsilon as a specific duration using different duration interpretations per bound
    ///
    /// # Errors
    ///
    /// If `start_epsilon_duration` + `end_epsilon_duration` overflows,
    /// the method returns [`DurationOverflow`](EpsilonInterpretationDurationError::DurationOverflow).
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::{Epsilon, EpsilonInterpretationDurationError};
    /// let start_epsilon_duration = chrono::Duration::seconds(1);
    /// let end_epsilon_duration = chrono::Duration::seconds(2);
    ///
    /// assert_eq!(
    ///     Epsilon::None.interpret_as_duration_bound_specific(start_epsilon_duration, end_epsilon_duration),
    ///     Ok(chrono::Duration::zero()),
    /// );
    /// assert_eq!(
    ///     Epsilon::Start.interpret_as_duration_bound_specific(start_epsilon_duration, end_epsilon_duration),
    ///     Ok(start_epsilon_duration),
    /// );
    /// assert_eq!(
    ///     Epsilon::End.interpret_as_duration_bound_specific(start_epsilon_duration, end_epsilon_duration),
    ///     Ok(end_epsilon_duration),
    /// );
    /// assert_eq!(
    ///     Epsilon::Both.interpret_as_duration_bound_specific(start_epsilon_duration, end_epsilon_duration),
    ///     Ok(start_epsilon_duration + end_epsilon_duration)
    /// );
    /// ```
    pub fn interpret_as_duration_bound_specific(
        &self,
        start_epsilon_duration: chrono::Duration,
        end_epsilon_duration: chrono::Duration,
    ) -> Result<chrono::Duration, EpsilonInterpretationDurationError> {
        match self {
            Self::None => Ok(chrono::Duration::zero()),
            Self::Start => Ok(start_epsilon_duration),
            Self::End => Ok(end_epsilon_duration),
            Self::Both => start_epsilon_duration
                .checked_add(&end_epsilon_duration)
                .ok_or(EpsilonInterpretationDurationError::DurationOverflow),
        }
    }

    /// Interprets the epsilon as a specific duration using the given duration
    ///
    /// # Errors
    ///
    /// If `epsilon_duration * 2` overflows,
    /// the method returns [`DurationOverflow`](EpsilonInterpretationDurationError::DurationOverflow).
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::{Epsilon, EpsilonInterpretationDurationError};
    /// let epsilon_duration = chrono::Duration::seconds(1);
    ///
    /// assert_eq!(
    ///     Epsilon::None.interpret_as_duration(epsilon_duration),
    ///     Ok(chrono::Duration::zero()),
    /// );
    /// assert_eq!(
    ///     Epsilon::Start.interpret_as_duration(epsilon_duration),
    ///     Ok(epsilon_duration),
    /// );
    /// assert_eq!(
    ///     Epsilon::End.interpret_as_duration(epsilon_duration),
    ///     Ok(epsilon_duration),
    /// );
    /// assert_eq!(
    ///     Epsilon::Both.interpret_as_duration(epsilon_duration),
    ///     Ok(epsilon_duration * 2),
    /// );
    /// ```
    pub fn interpret_as_duration(
        &self,
        epsilon_duration: chrono::Duration,
    ) -> Result<chrono::Duration, EpsilonInterpretationDurationError> {
        self.interpret_as_duration_bound_specific(epsilon_duration, epsilon_duration)
    }
}

impl Display for Epsilon {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::None => write!(f, "No epsilons"),
            Self::Start => write!(f, "Epsilon on start bound"),
            Self::End => write!(f, "Epsilon on end bound"),
            Self::Both => write!(f, "Epsilon on both bounds"),
        }
    }
}

/// Converts `(BoundInclusivity, BoundInclusivity)` into [`Epsilon`]
///
/// The tuple elements represent the start bound inclusivity and end bound inclusivity, respectively.
/// Exclusive bounds, [`BoundInclusivity::Exclusive`], create an epsilon.
impl From<(BoundInclusivity, BoundInclusivity)> for Epsilon {
    fn from((start_inclusivity, end_inclusivity): (BoundInclusivity, BoundInclusivity)) -> Self {
        match (start_inclusivity, end_inclusivity) {
            (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive) => Epsilon::None,
            (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => Epsilon::Start,
            (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive) => Epsilon::End,
            (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => Epsilon::Both,
        }
    }
}

/// Converts `(bool, bool)` into [`Epsilon`]
///
/// The first tuple element represents whether the start bound has an epsilon,
/// the second tuple element represents whether the end bound has an epsilon.
impl From<(bool, bool)> for Epsilon {
    fn from((start_has_epsilon, end_has_epsilon): (bool, bool)) -> Self {
        match (start_has_epsilon, end_has_epsilon) {
            (false, false) => Epsilon::None,
            (true, false) => Epsilon::Start,
            (false, true) => Epsilon::End,
            (true, true) => Epsilon::Both,
        }
    }
}

/// Errors that can occur when [`Epsilon`] is interpreted as a duration
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EpsilonInterpretationDurationError {
    /// Duration interpretation overflowed
    DurationOverflow,
}

impl Display for EpsilonInterpretationDurationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DurationOverflow => write!(f, "Epsilon interpretation made `chrono::Duration` overflow"),
        }
    }
}

impl Error for EpsilonInterpretationDurationError {}

/// Interval duration
///
/// Supports `chrono`'s [`Duration`](chrono::Duration) for finite durations and supports
/// representation for infinite durations.
///
/// [`Finite`](Duration::Finite) supports infinitesimal duration variations, also known as [`Epsilon`]s,
/// created by the use of [exclusive bounds](BoundInclusivity::Exclusive).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum Duration {
    /// Finite duration
    Finite(chrono::Duration, Epsilon),
    /// Infinite duration
    Infinite,
}

impl Duration {
    /// Returns whether the interval duration is finite
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::{Duration, Epsilon};
    /// assert!(Duration::Finite(chrono::Duration::hours(1), Epsilon::None).is_finite());
    /// ```
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Duration::Finite(..))
    }

    /// Returns the content of the [`Finite`](Duration::Finite) variant
    ///
    /// Consumes `self` and puts the content of the [`Finite`](Duration::Finite) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::{Duration, Epsilon};
    /// assert_eq!(
    ///     Duration::Finite(chrono::Duration::hours(2), Epsilon::End).finite(),
    ///     Some((chrono::Duration::hours(2), Epsilon::End)),
    /// );
    /// assert_eq!(Duration::Infinite.finite(), None);
    /// ```
    #[must_use]
    pub fn finite(self) -> Option<(chrono::Duration, Epsilon)> {
        match self {
            Self::Finite(duration, epsilon) => Some((duration, epsilon)),
            Self::Infinite => None,
        }
    }

    /// Returns the content of the [`Finite`](Duration::Finite) variant and subtracts interpreted epsilon duration
    /// from it
    ///
    /// Consumes `self`, then uses the content of the [`Finite`](Duration::Finite) variant to compute the final
    /// interpreted duration, using [`Epsilon::interpret_as_duration`] under the hood,
    /// and puts the result in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// If [`Epsilon::interpret_as_duration`] returns an [`Err`], then the method returns [`None`].
    ///
    /// If the duration is small or if the interpreted [`Epsilon`]\(s) are larger than the duration, resulting
    /// in a negative duration, the duration defaults to [an empty duration](chrono::Duration::zero).
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::{Duration, Epsilon};
    /// let epsilon_duration = chrono::Duration::seconds(1);
    /// let large_epsilon_duration = chrono::Duration::hours(2);
    ///
    /// assert_eq!(
    ///     Duration::Finite(chrono::Duration::hours(1), Epsilon::End)
    ///     .finite_interpret_epsilon(epsilon_duration),
    ///     Some(chrono::Duration::minutes(59) + chrono::Duration::seconds(59)),
    /// );
    /// assert_eq!(
    ///     Duration::Infinite.finite_interpret_epsilon(epsilon_duration),
    ///     None,
    /// );
    /// assert_eq!(
    ///     Duration::Finite(chrono::Duration::hours(1), Epsilon::Start)
    ///     .finite_interpret_epsilon(large_epsilon_duration),
    ///     Some(chrono::Duration::zero()),
    /// );
    /// ```
    #[must_use]
    pub fn finite_interpret_epsilon(self, epsilon_duration: chrono::Duration) -> Option<chrono::Duration> {
        let (duration, epsilon) = self.finite()?;
        let Ok(interpreted_epsilon) = epsilon.interpret_as_duration(epsilon_duration) else {
            return None;
        };

        duration
            .checked_sub(&interpreted_epsilon)
            .map(|dur| dur.max(chrono::Duration::zero()))
    }

    /// Returns the [`chrono::Duration`] of the [`Finite`](Duration::Finite) variant and strips the epsilon duration
    ///
    /// Consumes `self`, then simply returns the [`chrono::Duration`] stored in the [`Finite`](Duration::Finite)
    /// variant, without using the stored [`Epsilon`]. Puts the result in an [`Option`].
    /// If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::{Duration, Epsilon};
    /// assert_eq!(
    ///     Duration::Finite(chrono::Duration::hours(2), Epsilon::Both).finite_strip_epsilon(),
    ///     Some(chrono::Duration::hours(2)),
    /// );
    /// assert_eq!(Duration::Infinite.finite_strip_epsilon(), None);
    /// ```
    #[must_use]
    pub fn finite_strip_epsilon(self) -> Option<chrono::Duration> {
        Some(self.finite()?.0)
    }
}

impl Display for Duration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Finite(duration, epsilon) => write!(f, "Finite duration: {duration} ({epsilon})"),
            Self::Infinite => write!(f, "Infinite duration"),
        }
    }
}

impl From<chrono::Duration> for Duration {
    fn from(duration: chrono::Duration) -> Self {
        Duration::Finite(duration, Epsilon::default())
    }
}

impl From<(chrono::Duration, Epsilon)> for Duration {
    fn from((duration, epsilon): (chrono::Duration, Epsilon)) -> Self {
        Duration::Finite(duration, epsilon)
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
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
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

//! Special intervals
//!
//! Includes intervals that are not absolute nor relative: [`UnboundedInterval`]
//! and [`EmptyInterval`].

use std::error::Error;
use std::fmt::Display;
use std::ops::RangeFull;
use std::time::Duration as StdDuration;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use super::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use super::meta::{
    Duration as IntervalDuration,
    HasDuration,
    HasOpenness,
    HasRelativity,
    IsEmpty,
    Openness,
    Relativity,
};
use super::relative::{
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeInterval,
    RelativeStartBound,
};
use crate::intervals::meta::{Epsilon, Interval};

/// An unbounded interval
///
/// Interval without [`Relativity`] (not absolute nor relative) and without any
/// bounds. Is equivalent to _time itself_ (all time), infinite duration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct UnboundedInterval;

impl UnboundedInterval {
    /// Converts `self` into an [`AbsoluteBoundPair`]
    #[must_use]
    pub fn to_abs_bound_pair(self) -> AbsoluteBoundPair {
        AbsoluteBoundPair::from(self)
    }

    /// Converts `self` into an [`EmptiableAbsoluteBoundPair`]
    #[must_use]
    pub fn to_emptiable_abs_bound_pair(self) -> EmptiableAbsoluteBoundPair {
        EmptiableAbsoluteBoundPair::from(self)
    }

    /// Converts `self` into an [`AbsoluteInterval`]
    #[must_use]
    pub fn to_abs_interval(self) -> AbsoluteInterval {
        AbsoluteInterval::from(self)
    }

    /// Converts `self` into an [`EmptiableAbsoluteInterval`]
    #[must_use]
    pub fn to_emptiable_abs_interval(self) -> EmptiableAbsoluteInterval {
        EmptiableAbsoluteInterval::from(self)
    }

    /// Converts `self` into an [`RelativeBoundPair`]
    #[must_use]
    pub fn to_rel_bound_pair(self) -> RelativeBoundPair {
        RelativeBoundPair::from(self)
    }

    /// Converts `self` into an [`EmptiableRelativeBoundPair`]
    #[must_use]
    pub fn to_emptiable_rel_bound_pair(self) -> EmptiableRelativeBoundPair {
        EmptiableRelativeBoundPair::from(self)
    }

    /// Converts `self` into an [`RelativeInterval`]
    #[must_use]
    pub fn to_rel_interval(self) -> RelativeInterval {
        RelativeInterval::from(self)
    }

    /// Converts `self` into an [`EmptiableRelativeInterval`]
    #[must_use]
    pub fn to_emptiable_rel_interval(self) -> EmptiableRelativeInterval {
        EmptiableRelativeInterval::from(self)
    }
}

impl Interval for UnboundedInterval {}

impl HasOpenness for UnboundedInterval {
    fn openness(&self) -> Openness {
        Openness::Unbounded
    }
}

impl HasRelativity for UnboundedInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Any
    }
}

impl HasDuration for UnboundedInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasAbsoluteBoundPair for UnboundedInterval {
    fn abs_bound_pair(&self) -> AbsoluteBoundPair {
        AbsoluteBoundPair::new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        AbsoluteStartBound::InfinitePast
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        AbsoluteEndBound::InfiniteFuture
    }
}

impl HasRelativeBoundPair for UnboundedInterval {
    fn rel_bound_pair(&self) -> RelativeBoundPair {
        RelativeBoundPair::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelativeStartBound {
        RelativeStartBound::InfinitePast
    }

    fn rel_end(&self) -> RelativeEndBound {
        RelativeEndBound::InfiniteFuture
    }
}

impl From<RangeFull> for UnboundedInterval {
    fn from(_value: RangeFull) -> Self {
        UnboundedInterval
    }
}

/// Error that can occur when trying to convert [`AbsoluteBoundPair`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromAbsoluteBoundPairError;

impl Display for UnboundedIntervalTryFromAbsoluteBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsoluteBoundPair` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromAbsoluteBoundPairError {}

impl TryFrom<AbsoluteBoundPair> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromAbsoluteBoundPairError;

    fn try_from(value: AbsoluteBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture) => Ok(UnboundedInterval),
            _ => Err(UnboundedIntervalTryFromAbsoluteBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`RelativeBoundPair`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromRelativeBoundPairError;

impl Display for UnboundedIntervalTryFromRelativeBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelativeBoundPair` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromRelativeBoundPairError {}

impl TryFrom<RelativeBoundPair> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromRelativeBoundPairError;

    fn try_from(value: RelativeBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture) => Ok(UnboundedInterval),
            _ => Err(UnboundedIntervalTryFromRelativeBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsoluteBoundPair`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromEmptiableAbsoluteBoundPairError;

impl Display for UnboundedIntervalTryFromEmptiableAbsoluteBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsoluteBoundPair` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromEmptiableAbsoluteBoundPairError {}

impl TryFrom<EmptiableAbsoluteBoundPair> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromEmptiableAbsoluteBoundPairError;

    fn try_from(value: EmptiableAbsoluteBoundPair) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(UnboundedIntervalTryFromEmptiableAbsoluteBoundPairError)?,
        )
        .or(Err(UnboundedIntervalTryFromEmptiableAbsoluteBoundPairError))
    }
}

/// Error that can occur when trying to convert [`EmptiableRelativeBoundPair`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromEmptiableRelativeBoundPairError;

impl Display for UnboundedIntervalTryFromEmptiableRelativeBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelativeBoundPair` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromEmptiableRelativeBoundPairError {}

impl TryFrom<EmptiableRelativeBoundPair> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromEmptiableRelativeBoundPairError;

    fn try_from(value: EmptiableRelativeBoundPair) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(UnboundedIntervalTryFromEmptiableRelativeBoundPairError)?,
        )
        .or(Err(UnboundedIntervalTryFromEmptiableRelativeBoundPairError))
    }
}

/// Error that can occur when trying to convert [`AbsoluteInterval`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromAbsoluteIntervalError;

impl Display for UnboundedIntervalTryFromAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsoluteInterval` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromAbsoluteIntervalError {}

impl TryFrom<AbsoluteInterval> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromAbsoluteIntervalError;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        value.unbounded().ok_or(UnboundedIntervalTryFromAbsoluteIntervalError)
    }
}

/// Error that can occur when trying to convert [`RelativeInterval`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromRelativeIntervalError;

impl Display for UnboundedIntervalTryFromRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelativeInterval` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromRelativeIntervalError {}

impl TryFrom<RelativeInterval> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromRelativeIntervalError;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        value.unbounded().ok_or(UnboundedIntervalTryFromRelativeIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsoluteInterval`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromEmptiableAbsoluteIntervalError;

impl Display for UnboundedIntervalTryFromEmptiableAbsoluteIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsoluteInterval` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromEmptiableAbsoluteIntervalError {}

impl TryFrom<EmptiableAbsoluteInterval> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromEmptiableAbsoluteIntervalError;

    fn try_from(value: EmptiableAbsoluteInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(UnboundedIntervalTryFromEmptiableAbsoluteIntervalError)?,
        )
        .or(Err(UnboundedIntervalTryFromEmptiableAbsoluteIntervalError))
    }
}

/// Error that can occur when trying to convert [`EmptiableRelativeInterval`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromEmptiableRelativeIntervalError;

impl Display for UnboundedIntervalTryFromEmptiableRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelativeInterval` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromEmptiableRelativeIntervalError {}

impl TryFrom<EmptiableRelativeInterval> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromEmptiableRelativeIntervalError;

    fn try_from(value: EmptiableRelativeInterval) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(UnboundedIntervalTryFromEmptiableRelativeIntervalError)?,
        )
        .or(Err(UnboundedIntervalTryFromEmptiableRelativeIntervalError))
    }
}

/// Empty interval
///
/// Similar to the [empty set](https://en.wikipedia.org/wiki/Empty_set), this allows for still performing
/// operations such as the complement of the interval without issues, but the
/// difference between an empty set and and empty interval is that intervals are
/// linked to time, therefore empty intervals are out of this time dimension.
///
/// This means that, contrary to an empty set, an empty interval is **not** a
/// subset of any interval. It simply represents the _lack_ of a time interval,
/// like the complement of an unbounded interval.
///
/// In regards to operations such as the overlap position, or union, since an
/// empty interval has no defined place in time, it is always _outside_,
/// _separate_ from the compared.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct EmptyInterval;

impl EmptyInterval {
    /// Converts `self` into [`EmptiableAbsoluteBoundPair`]
    #[must_use]
    pub fn to_emptiable_abs_bound_pair(self) -> EmptiableAbsoluteBoundPair {
        EmptiableAbsoluteBoundPair::Empty
    }

    /// Converts `self` into [`EmptiableAbsoluteInterval`]
    #[must_use]
    pub fn to_emptiable_abs_interval(self) -> EmptiableAbsoluteInterval {
        EmptiableAbsoluteInterval::Empty(self)
    }

    /// Converts `self` into [`EmptiableRelativeBoundPair`]
    #[must_use]
    pub fn to_emptiable_rel_bound_pair(self) -> EmptiableRelativeBoundPair {
        EmptiableRelativeBoundPair::Empty
    }

    /// Converts `self` into [`EmptiableRelativeInterval`]
    #[must_use]
    pub fn to_emptiable_rel_interval(self) -> EmptiableRelativeInterval {
        EmptiableRelativeInterval::Empty(self)
    }
}

impl Interval for EmptyInterval {}

impl HasOpenness for EmptyInterval {
    fn openness(&self) -> Openness {
        Openness::Empty
    }
}

impl HasRelativity for EmptyInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Any
    }
}

impl HasDuration for EmptyInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Finite(StdDuration::ZERO, Epsilon::None)
    }
}

impl HasEmptiableAbsoluteBoundPair for EmptyInterval {
    fn emptiable_abs_bound_pair(&self) -> EmptiableAbsoluteBoundPair {
        EmptiableAbsoluteBoundPair::Empty
    }

    fn partial_abs_start(&self) -> Option<AbsoluteStartBound> {
        None
    }

    fn partial_abs_end(&self) -> Option<AbsoluteEndBound> {
        None
    }
}

impl HasEmptiableRelativeBoundPair for EmptyInterval {
    fn emptiable_rel_bound_pair(&self) -> EmptiableRelativeBoundPair {
        EmptiableRelativeBoundPair::Empty
    }

    fn partial_rel_start(&self) -> Option<RelativeStartBound> {
        None
    }

    fn partial_rel_end(&self) -> Option<RelativeEndBound> {
        None
    }
}

impl IsEmpty for EmptyInterval {
    fn is_empty(&self) -> bool {
        true
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsoluteBoundPair`] into [`EmptyInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EmptyIntervalTryFromEmptiableAbsoluteBoundPair;

impl Display for EmptyIntervalTryFromEmptiableAbsoluteBoundPair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsoluteBoundPair` into `EmptyInterval`"
        )
    }
}

impl Error for EmptyIntervalTryFromEmptiableAbsoluteBoundPair {}

impl TryFrom<EmptiableAbsoluteBoundPair> for EmptyInterval {
    type Error = EmptyIntervalTryFromEmptiableAbsoluteBoundPair;

    fn try_from(value: EmptiableAbsoluteBoundPair) -> Result<Self, Self::Error> {
        value
            .is_empty()
            .then_some(EmptyInterval)
            .ok_or(EmptyIntervalTryFromEmptiableAbsoluteBoundPair)
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsoluteInterval`] into [`EmptyInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EmptyIntervalTryFromEmptiableAbsoluteInterval;

impl Display for EmptyIntervalTryFromEmptiableAbsoluteInterval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsoluteInterval` into `EmptyInterval`"
        )
    }
}

impl Error for EmptyIntervalTryFromEmptiableAbsoluteInterval {}

impl TryFrom<EmptiableAbsoluteInterval> for EmptyInterval {
    type Error = EmptyIntervalTryFromEmptiableAbsoluteInterval;

    fn try_from(value: EmptiableAbsoluteInterval) -> Result<Self, Self::Error> {
        value
            .is_empty()
            .then_some(EmptyInterval)
            .ok_or(EmptyIntervalTryFromEmptiableAbsoluteInterval)
    }
}

/// Error that can occur when trying to convert [`EmptiableRelativeBoundPair`] into [`EmptyInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EmptyIntervalTryFromEmptiableRelativeBoundPair;

impl Display for EmptyIntervalTryFromEmptiableRelativeBoundPair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelativeBoundPair` into `EmptyInterval`"
        )
    }
}

impl Error for EmptyIntervalTryFromEmptiableRelativeBoundPair {}

impl TryFrom<EmptiableRelativeBoundPair> for EmptyInterval {
    type Error = EmptyIntervalTryFromEmptiableRelativeBoundPair;

    fn try_from(value: EmptiableRelativeBoundPair) -> Result<Self, Self::Error> {
        value
            .is_empty()
            .then_some(EmptyInterval)
            .ok_or(EmptyIntervalTryFromEmptiableRelativeBoundPair)
    }
}

/// Error that can occur when trying to convert [`EmptiableRelativeInterval`] into [`EmptyInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EmptyIntervalTryFromEmptiableRelativeInterval;

impl Display for EmptyIntervalTryFromEmptiableRelativeInterval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelativeInterval` into `EmptyInterval`"
        )
    }
}

impl Error for EmptyIntervalTryFromEmptiableRelativeInterval {}

impl TryFrom<EmptiableRelativeInterval> for EmptyInterval {
    type Error = EmptyIntervalTryFromEmptiableRelativeInterval;

    fn try_from(value: EmptiableRelativeInterval) -> Result<Self, Self::Error> {
        value
            .is_empty()
            .then_some(EmptyInterval)
            .ok_or(EmptyIntervalTryFromEmptiableRelativeInterval)
    }
}

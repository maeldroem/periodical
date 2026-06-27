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
    AbsBoundPair,
    AbsEndBound,
    AbsInterval,
    AbsStartBound,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
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
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HasEmptiableRelBoundPair,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelInterval,
    RelStartBound,
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
    /// Converts `self` into an [`AbsBoundPair`]
    #[must_use]
    pub fn to_abs_bound_pair(self) -> AbsBoundPair {
        AbsBoundPair::from(self)
    }

    /// Converts `self` into an [`EmptiableAbsBoundPair`]
    #[must_use]
    pub fn to_emptiable_abs_bound_pair(self) -> EmptiableAbsBoundPair {
        EmptiableAbsBoundPair::from(self)
    }

    /// Converts `self` into an [`AbsInterval`]
    #[must_use]
    pub fn to_abs_interval(self) -> AbsInterval {
        AbsInterval::from(self)
    }

    /// Converts `self` into an [`EmptiableAbsInterval`]
    #[must_use]
    pub fn to_emptiable_abs_interval(self) -> EmptiableAbsInterval {
        EmptiableAbsInterval::from(self)
    }

    /// Converts `self` into an [`RelBoundPair`]
    #[must_use]
    pub fn to_rel_bound_pair(self) -> RelBoundPair {
        RelBoundPair::from(self)
    }

    /// Converts `self` into an [`EmptiableRelBoundPair`]
    #[must_use]
    pub fn to_emptiable_rel_bound_pair(self) -> EmptiableRelBoundPair {
        EmptiableRelBoundPair::from(self)
    }

    /// Converts `self` into an [`RelInterval`]
    #[must_use]
    pub fn to_rel_interval(self) -> RelInterval {
        RelInterval::from(self)
    }

    /// Converts `self` into an [`EmptiableRelInterval`]
    #[must_use]
    pub fn to_emptiable_rel_interval(self) -> EmptiableRelInterval {
        EmptiableRelInterval::from(self)
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

impl HasAbsBoundPair for UnboundedInterval {
    fn abs_bound_pair(&self) -> AbsBoundPair {
        AbsBoundPair::new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsStartBound {
        AbsStartBound::InfinitePast
    }

    fn abs_end(&self) -> AbsEndBound {
        AbsEndBound::InfiniteFuture
    }
}

impl HasRelBoundPair for UnboundedInterval {
    fn rel_bound_pair(&self) -> RelBoundPair {
        RelBoundPair::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelStartBound {
        RelStartBound::InfinitePast
    }

    fn rel_end(&self) -> RelEndBound {
        RelEndBound::InfiniteFuture
    }
}

impl From<RangeFull> for UnboundedInterval {
    fn from(_value: RangeFull) -> Self {
        UnboundedInterval
    }
}

/// Error that can occur when trying to convert [`AbsBoundPair`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromAbsBoundPairError;

impl Display for UnboundedIntervalTryFromAbsBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsBoundPair` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromAbsBoundPairError {}

impl TryFrom<AbsBoundPair> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromAbsBoundPairError;

    fn try_from(value: AbsBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture) => Ok(UnboundedInterval),
            _ => Err(UnboundedIntervalTryFromAbsBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`RelBoundPair`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromRelBoundPairError;

impl Display for UnboundedIntervalTryFromRelBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelBoundPair` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromRelBoundPairError {}

impl TryFrom<RelBoundPair> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromRelBoundPairError;

    fn try_from(value: RelBoundPair) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (RelStartBound::InfinitePast, RelEndBound::InfiniteFuture) => Ok(UnboundedInterval),
            _ => Err(UnboundedIntervalTryFromRelBoundPairError),
        }
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsBoundPair`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromEmptiableAbsBoundPairError;

impl Display for UnboundedIntervalTryFromEmptiableAbsBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsBoundPair` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromEmptiableAbsBoundPairError {}

impl TryFrom<EmptiableAbsBoundPair> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromEmptiableAbsBoundPairError;

    fn try_from(value: EmptiableAbsBoundPair) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(UnboundedIntervalTryFromEmptiableAbsBoundPairError)?,
        )
        .or(Err(UnboundedIntervalTryFromEmptiableAbsBoundPairError))
    }
}

/// Error that can occur when trying to convert [`EmptiableRelBoundPair`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromEmptiableRelBoundPairError;

impl Display for UnboundedIntervalTryFromEmptiableRelBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelBoundPair` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromEmptiableRelBoundPairError {}

impl TryFrom<EmptiableRelBoundPair> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromEmptiableRelBoundPairError;

    fn try_from(value: EmptiableRelBoundPair) -> Result<Self, Self::Error> {
        Self::try_from(
            value
                .bound()
                .ok_or(UnboundedIntervalTryFromEmptiableRelBoundPairError)?,
        )
        .or(Err(UnboundedIntervalTryFromEmptiableRelBoundPairError))
    }
}

/// Error that can occur when trying to convert [`AbsInterval`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromAbsIntervalError;

impl Display for UnboundedIntervalTryFromAbsIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `AbsInterval` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromAbsIntervalError {}

impl TryFrom<AbsInterval> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromAbsIntervalError;

    fn try_from(value: AbsInterval) -> Result<Self, Self::Error> {
        value.unbounded().ok_or(UnboundedIntervalTryFromAbsIntervalError)
    }
}

/// Error that can occur when trying to convert [`RelInterval`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromRelIntervalError;

impl Display for UnboundedIntervalTryFromRelIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `RelInterval` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromRelIntervalError {}

impl TryFrom<RelInterval> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromRelIntervalError;

    fn try_from(value: RelInterval) -> Result<Self, Self::Error> {
        value.unbounded().ok_or(UnboundedIntervalTryFromRelIntervalError)
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsInterval`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromEmptiableAbsIntervalError;

impl Display for UnboundedIntervalTryFromEmptiableAbsIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsInterval` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromEmptiableAbsIntervalError {}

impl TryFrom<EmptiableAbsInterval> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromEmptiableAbsIntervalError;

    fn try_from(value: EmptiableAbsInterval) -> Result<Self, Self::Error> {
        Self::try_from(value.bound().ok_or(UnboundedIntervalTryFromEmptiableAbsIntervalError)?)
            .or(Err(UnboundedIntervalTryFromEmptiableAbsIntervalError))
    }
}

/// Error that can occur when trying to convert [`EmptiableRelInterval`] into [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnboundedIntervalTryFromEmptiableRelIntervalError;

impl Display for UnboundedIntervalTryFromEmptiableRelIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelInterval` into `UnboundedInterval`"
        )
    }
}

impl Error for UnboundedIntervalTryFromEmptiableRelIntervalError {}

impl TryFrom<EmptiableRelInterval> for UnboundedInterval {
    type Error = UnboundedIntervalTryFromEmptiableRelIntervalError;

    fn try_from(value: EmptiableRelInterval) -> Result<Self, Self::Error> {
        Self::try_from(value.bound().ok_or(UnboundedIntervalTryFromEmptiableRelIntervalError)?)
            .or(Err(UnboundedIntervalTryFromEmptiableRelIntervalError))
    }
}

/// Empty interval
///
/// Similar to the [empty set](https://en.wikipedia.org/w/index.php?title=Empty_set&oldid=1336567852),
/// this allows for still performing operations such as the complement of the interval without issues,
/// but the difference between an empty set and and empty interval is that intervals are
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
    /// Converts `self` into [`EmptiableAbsBoundPair`]
    #[must_use]
    pub fn to_emptiable_abs_bound_pair(self) -> EmptiableAbsBoundPair {
        EmptiableAbsBoundPair::Empty
    }

    /// Converts `self` into [`EmptiableAbsInterval`]
    #[must_use]
    pub fn to_emptiable_abs_interval(self) -> EmptiableAbsInterval {
        EmptiableAbsInterval::Empty(self)
    }

    /// Converts `self` into [`EmptiableRelBoundPair`]
    #[must_use]
    pub fn to_emptiable_rel_bound_pair(self) -> EmptiableRelBoundPair {
        EmptiableRelBoundPair::Empty
    }

    /// Converts `self` into [`EmptiableRelInterval`]
    #[must_use]
    pub fn to_emptiable_rel_interval(self) -> EmptiableRelInterval {
        EmptiableRelInterval::Empty(self)
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

impl HasEmptiableAbsBoundPair for EmptyInterval {
    fn emptiable_abs_bound_pair(&self) -> EmptiableAbsBoundPair {
        EmptiableAbsBoundPair::Empty
    }

    fn partial_abs_start(&self) -> Option<AbsStartBound> {
        None
    }

    fn partial_abs_end(&self) -> Option<AbsEndBound> {
        None
    }
}

impl HasEmptiableRelBoundPair for EmptyInterval {
    fn emptiable_rel_bound_pair(&self) -> EmptiableRelBoundPair {
        EmptiableRelBoundPair::Empty
    }

    fn partial_rel_start(&self) -> Option<RelStartBound> {
        None
    }

    fn partial_rel_end(&self) -> Option<RelEndBound> {
        None
    }
}

impl IsEmpty for EmptyInterval {
    fn is_empty(&self) -> bool {
        true
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsBoundPair`] into [`EmptyInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EmptyIntervalTryFromEmptiableAbsBoundPair;

impl Display for EmptyIntervalTryFromEmptiableAbsBoundPair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsBoundPair` into `EmptyInterval`"
        )
    }
}

impl Error for EmptyIntervalTryFromEmptiableAbsBoundPair {}

impl TryFrom<EmptiableAbsBoundPair> for EmptyInterval {
    type Error = EmptyIntervalTryFromEmptiableAbsBoundPair;

    fn try_from(value: EmptiableAbsBoundPair) -> Result<Self, Self::Error> {
        value
            .is_empty()
            .then_some(EmptyInterval)
            .ok_or(EmptyIntervalTryFromEmptiableAbsBoundPair)
    }
}

/// Error that can occur when trying to convert [`EmptiableAbsInterval`] into [`EmptyInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EmptyIntervalTryFromEmptiableAbsInterval;

impl Display for EmptyIntervalTryFromEmptiableAbsInterval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableAbsInterval` into `EmptyInterval`"
        )
    }
}

impl Error for EmptyIntervalTryFromEmptiableAbsInterval {}

impl TryFrom<EmptiableAbsInterval> for EmptyInterval {
    type Error = EmptyIntervalTryFromEmptiableAbsInterval;

    fn try_from(value: EmptiableAbsInterval) -> Result<Self, Self::Error> {
        value
            .is_empty()
            .then_some(EmptyInterval)
            .ok_or(EmptyIntervalTryFromEmptiableAbsInterval)
    }
}

/// Error that can occur when trying to convert [`EmptiableRelBoundPair`] into [`EmptyInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EmptyIntervalTryFromEmptiableRelBoundPair;

impl Display for EmptyIntervalTryFromEmptiableRelBoundPair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelBoundPair` into `EmptyInterval`"
        )
    }
}

impl Error for EmptyIntervalTryFromEmptiableRelBoundPair {}

impl TryFrom<EmptiableRelBoundPair> for EmptyInterval {
    type Error = EmptyIntervalTryFromEmptiableRelBoundPair;

    fn try_from(value: EmptiableRelBoundPair) -> Result<Self, Self::Error> {
        value
            .is_empty()
            .then_some(EmptyInterval)
            .ok_or(EmptyIntervalTryFromEmptiableRelBoundPair)
    }
}

/// Error that can occur when trying to convert [`EmptiableRelInterval`] into [`EmptyInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EmptyIntervalTryFromEmptiableRelInterval;

impl Display for EmptyIntervalTryFromEmptiableRelInterval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "An error occurred when trying to convert `EmptiableRelInterval` into `EmptyInterval`"
        )
    }
}

impl Error for EmptyIntervalTryFromEmptiableRelInterval {}

impl TryFrom<EmptiableRelInterval> for EmptyInterval {
    type Error = EmptyIntervalTryFromEmptiableRelInterval;

    fn try_from(value: EmptiableRelInterval) -> Result<Self, Self::Error> {
        value
            .is_empty()
            .then_some(EmptyInterval)
            .ok_or(EmptyIntervalTryFromEmptiableRelInterval)
    }
}

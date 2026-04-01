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
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use super::meta::{
    Duration as IntervalDuration,
    IsEmpty,
    HasDuration,
    HasOpenness,
    HasRelativity,
    Openness,
    Relativity,
};
use super::relative::{
    EmptiableRelativeBoundPair,
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

/// Error that can occur when trying to convert an [`AbsoluteInterval`] or
/// [`RelativeInterval`] into an [`UnboundedInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnboundedIntervalConversionErr {
    WrongVariant,
}

impl Display for UnboundedIntervalConversionErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for UnboundedIntervalConversionErr {}

impl TryFrom<AbsoluteInterval> for UnboundedInterval {
    type Error = UnboundedIntervalConversionErr;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::Unbounded(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<RelativeInterval> for UnboundedInterval {
    type Error = UnboundedIntervalConversionErr;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::Unbounded(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
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

/// Errors that can occur when trying to convert an [`AbsoluteInterval`] or
/// [`RelativeInterval`] into an [`EmptyInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EmptyIntervalConversionErr {
    WrongVariant,
}

impl Display for EmptyIntervalConversionErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for EmptyIntervalConversionErr {}

/*
IMPL TRY FROM ON Emptiable VARIANTS OF INTERVALS
impl TryFrom<AbsoluteInterval> for EmptyInterval {
    type Error = EmptyIntervalConversionErr;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::Empty(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<RelativeInterval> for EmptyInterval {
    type Error = EmptyIntervalConversionErr;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::Empty(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}
*/

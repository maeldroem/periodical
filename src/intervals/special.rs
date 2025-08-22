//! Special intervals
//!
//! Unbounded and empty intervals

use std::error::Error;
use std::fmt::Display;
use std::ops::RangeFull;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use chrono::Duration;

use crate::intervals::meta::Interval;

use super::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, EmptiableAbsoluteBounds, HasAbsoluteBounds,
    HasEmptiableAbsoluteBounds,
};
use super::meta::{Duration as IntervalDuration, Openness, Relativity};
use super::prelude::*;
use super::relative::{
    EmptiableRelativeBounds, HasEmptiableRelativeBounds, HasRelativeBounds, RelativeBounds, RelativeEndBound,
    RelativeInterval, RelativeStartBound,
};

/// An unbounded interval
///
/// Interval without relativity (not absolute nor relative) and without any bounds.
/// Is equivalent to _time itself_ (all time), infinite duration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
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

impl HasAbsoluteBounds for UnboundedInterval {
    fn abs_bounds(&self) -> AbsoluteBounds {
        AbsoluteBounds::new(self.abs_start(), self.abs_end())
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        AbsoluteStartBound::InfinitePast
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        AbsoluteEndBound::InfiniteFuture
    }
}

impl HasRelativeBounds for UnboundedInterval {
    fn rel_bounds(&self) -> RelativeBounds {
        RelativeBounds::new(self.rel_start(), self.rel_end())
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

/// No interval
///
/// Similar to the [empty set](https://en.wikipedia.org/wiki/Empty_set), this allows for still performing
/// operations such as the complement of the interval without issues, but the difference between an empty set and
/// and empty interval is that intervals are linked to time, therefore empty intervals are out of this time dimension.
///
/// This means that, contrary to an empty set, an empty interval is **not** a subset of any interval.
/// It simply represents the _lack_ of a time interval, like the complement of an unbounded interval.
///
/// In regards to operations such as the overlap position, or union, since an empty interval has no defined place
/// in time, it is always _outside_, _separate_ from the compared.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
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
        IntervalDuration::Finite(Duration::zero())
    }
}

impl HasEmptiableAbsoluteBounds for EmptyInterval {
    fn emptiable_abs_bounds(&self) -> EmptiableAbsoluteBounds {
        EmptiableAbsoluteBounds::Empty
    }

    fn partial_abs_start(&self) -> Option<AbsoluteStartBound> {
        None
    }

    fn partial_abs_end(&self) -> Option<AbsoluteEndBound> {
        None
    }
}

impl HasEmptiableRelativeBounds for EmptyInterval {
    fn emptiable_rel_bounds(&self) -> EmptiableRelativeBounds {
        EmptiableRelativeBounds::Empty
    }

    fn partial_rel_start(&self) -> Option<RelativeStartBound> {
        None
    }

    fn partial_rel_end(&self) -> Option<RelativeEndBound> {
        None
    }
}

impl Emptiable for EmptyInterval {
    fn is_empty(&self) -> bool {
        true
    }
}

impl From<()> for EmptyInterval {
    fn from(_value: ()) -> Self {
        EmptyInterval
    }
}

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

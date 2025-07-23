//! Special intervals
//!
//! Open and empty intervals

use std::error::Error;
use std::fmt::Display;

use chrono::Duration;

use crate::intervals::meta::Interval;

use super::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteInterval, AbsoluteStartBound, EmptiableAbsoluteBounds, HasAbsoluteBounds,
    HasEmptiableAbsoluteBounds,
};
use super::meta::{Duration as IntervalDuration, HasDuration, HasOpenness, HasRelativity, Openness, Relativity};
use super::relative::{
    EmptiableRelativeBounds, HasEmptiableRelativeBounds, HasRelativeBounds, RelativeBounds, RelativeEndBound,
    RelativeInterval, RelativeStartBound,
};

/// An open interval
///
/// Interval without relativity (not absolute nor relative) and without any bounds.
/// Is equivalent to _time itself_ (all time), infinite duration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OpenInterval;

impl Interval for OpenInterval {}

impl HasOpenness for OpenInterval {
    fn openness(&self) -> Openness {
        Openness::Open
    }
}

impl HasRelativity for OpenInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Any
    }
}

impl HasDuration for OpenInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasAbsoluteBounds for OpenInterval {
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

impl HasRelativeBounds for OpenInterval {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpenIntervalConversionErr {
    WrongVariant,
}

impl Display for OpenIntervalConversionErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for OpenIntervalConversionErr {}

impl TryFrom<AbsoluteInterval> for OpenInterval {
    type Error = OpenIntervalConversionErr;

    fn try_from(value: AbsoluteInterval) -> Result<Self, Self::Error> {
        match value {
            AbsoluteInterval::Open(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

impl TryFrom<RelativeInterval> for OpenInterval {
    type Error = OpenIntervalConversionErr;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::Open(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

/// No interval
///
/// Equivalent to the [empty set](https://en.wikipedia.org/wiki/Empty_set), this allows for still performing
/// operations such as the complement of the interval without issues.
///
/// In regards to operations such as the overlap position, an empty interval has no defined place,
/// it simply represents the _lack_ of a time interval, like the complement of an open interval
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

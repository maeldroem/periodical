//! Absolute interval
//!
//! Represents any form of specific absolute intervals,
//! besides [`EmptyInterval`](crate::intervals::special::EmptyInterval).
//! That includes [`BoundedAbsoluteInterval`], [`HalfBoundedAbsoluteInterval`],
//! and [`UnboundedInterval`].
//!
//! The contained intervals conserve the [openness](Openness) invariant, but the
//! chosen variant can change. Compared to [`AbsoluteBoundPair`], thanks to the
//! variants we know exactly the kind of interval that is stored without needing
//! to check inner data.
//!
//! Usually this structure is for dealing with absolute intervals as a single
//! type in a way that conserves the [openness](Openness) invariant, contrary to
//! [`AbsoluteBoundPair`].
//!
//! If you want to include
//! [`EmptyInterval`](crate::intervals::special::EmptyInterval) as a possible
//! variant, see [`EmptiableAbsoluteInterval`].

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::{Bound, RangeBounds};

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::Timestamp;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    Emptiable,
    HasDuration,
    HasOpenness,
    HasRelativity,
    Interval,
    OpeningDirection,
    Openness,
    Relativity,
};
use crate::intervals::special::UnboundedInterval;

/// Absolute interval
///
/// Represents any form of specific absolute intervals,
/// besides [`EmptyInterval`](crate::intervals::special::EmptyInterval).
/// That includes [`BoundedAbsoluteInterval`], [`HalfBoundedAbsoluteInterval`],
/// and [`UnboundedInterval`].
///
/// The contained intervals conserve the [openness](Openness) invariant, but the
/// chosen variant can change. Compared to [`AbsoluteBoundPair`], thanks to the
/// variants we know exactly the kind of interval that is stored without needing
/// to check inner data.
///
/// Usually this structure is for dealing with absolute intervals as a single
/// type in a way that conserves the [openness](Openness) invariant, contrary to
/// [`AbsoluteBoundPair`].
///
/// If you want to include
/// [`EmptyInterval`](crate::intervals::special::EmptyInterval) as a possible
/// variant, see [`EmptiableAbsoluteInterval`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum AbsoluteInterval {
    Bounded(BoundedAbsoluteInterval),
    HalfBounded(HalfBoundedAbsoluteInterval),
    Unbounded(UnboundedInterval),
}

impl AbsoluteInterval {
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<Timestamp>,
    {
        match (range.start_bound().cloned(), range.end_bound().cloned()) {
            (Bound::Included(start), Bound::Included(end)) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Inclusive,
                    end,
                    BoundInclusivity::Inclusive,
                ))
            },
            (Bound::Included(start), Bound::Excluded(end)) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Inclusive,
                    end,
                    BoundInclusivity::Exclusive,
                ))
            },
            (Bound::Excluded(start), Bound::Included(end)) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Exclusive,
                    end,
                    BoundInclusivity::Inclusive,
                ))
            },
            (Bound::Excluded(start), Bound::Excluded(end)) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Exclusive,
                    end,
                    BoundInclusivity::Exclusive,
                ))
            },
            (Bound::Included(start), Bound::Unbounded) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToFuture,
                ))
            },
            (Bound::Excluded(start), Bound::Unbounded) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                ))
            },
            (Bound::Unbounded, Bound::Included(start)) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToPast,
                ))
            },
            (Bound::Unbounded, Bound::Excluded(start)) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                ))
            },
            (Bound::Unbounded, Bound::Unbounded) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }

    /// Compares two [`AbsoluteInterval`], but if they have the same start,
    /// order by decreasing length
    ///
    /// Uses [`EmptiableAbsoluteBoundPair::ord_by_start_and_inv_length`] under
    /// the hood.
    ///
    /// Don't rely on this method for checking for equality of start, as it will
    /// produce other [`Ordering`]s if their lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::AbsoluteInterval;
    /// # let mut bounds: [AbsoluteInterval; 0] = [];
    /// bounds.sort_by(AbsoluteInterval::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        self.abs_bound_pair()
            .ord_by_start_and_inv_length(&other.abs_bound_pair())
    }

    /// Wraps the interval in [`EmptiableAbsoluteInterval`]
    #[must_use]
    pub fn to_emptiable(self) -> EmptiableAbsoluteInterval {
        EmptiableAbsoluteInterval::from(self)
    }
}

impl Interval for AbsoluteInterval {}

impl HasAbsoluteBoundPair for AbsoluteInterval {
    fn abs_bound_pair(&self) -> AbsoluteBoundPair {
        match self {
            Self::Bounded(bounded) => bounded.abs_bound_pair(),
            Self::HalfBounded(half_bounded) => half_bounded.abs_bound_pair(),
            Self::Unbounded(unbounded) => unbounded.abs_bound_pair(),
        }
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        match self {
            Self::Bounded(bounded) => bounded.abs_start(),
            Self::HalfBounded(half_bounded) => half_bounded.abs_start(),
            Self::Unbounded(unbounded) => unbounded.abs_start(),
        }
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        match self {
            Self::Bounded(bounded) => bounded.abs_end(),
            Self::HalfBounded(half_bounded) => half_bounded.abs_end(),
            Self::Unbounded(unbounded) => unbounded.abs_end(),
        }
    }
}

impl HasDuration for AbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bounded(interval) => interval.duration(),
            Self::HalfBounded(interval) => interval.duration(),
            Self::Unbounded(interval) => interval.duration(),
        }
    }
}

impl HasRelativity for AbsoluteInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bounded(interval) => interval.relativity(),
            Self::HalfBounded(interval) => interval.relativity(),
            Self::Unbounded(interval) => interval.relativity(),
        }
    }
}

impl HasOpenness for AbsoluteInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Bounded(interval) => interval.openness(),
            Self::HalfBounded(interval) => interval.openness(),
            Self::Unbounded(interval) => interval.openness(),
        }
    }
}

impl PartialOrd for AbsoluteInterval {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteInterval {
    fn cmp(&self, other: &Self) -> Ordering {
        self.abs_bound_pair().cmp(&other.abs_bound_pair())
    }
}

impl Emptiable for AbsoluteInterval {
    fn is_empty(&self) -> bool {
        false
    }
}

impl From<BoundedAbsoluteInterval> for AbsoluteInterval {
    fn from(value: BoundedAbsoluteInterval) -> Self {
        AbsoluteInterval::Bounded(value)
    }
}

impl From<HalfBoundedAbsoluteInterval> for AbsoluteInterval {
    fn from(value: HalfBoundedAbsoluteInterval) -> Self {
        AbsoluteInterval::HalfBounded(value)
    }
}

impl From<UnboundedInterval> for AbsoluteInterval {
    fn from(value: UnboundedInterval) -> Self {
        AbsoluteInterval::Unbounded(value)
    }
}

impl From<AbsoluteBoundPair> for AbsoluteInterval {
    fn from(value: AbsoluteBoundPair) -> Self {
        type StartB = AbsoluteStartBound;
        type EndB = AbsoluteEndBound;

        match (value.abs_start(), value.abs_end()) {
            (StartB::InfinitePast, EndB::InfiniteFuture) => AbsoluteInterval::Unbounded(UnboundedInterval),
            (
                StartB::InfinitePast,
                EndB::Finite(AbsoluteFiniteBound {
                    time,
                    inclusivity,
                }),
            ) => AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                time,
                inclusivity,
                OpeningDirection::ToPast,
            )),
            (
                StartB::Finite(AbsoluteFiniteBound {
                    time,
                    inclusivity,
                }),
                EndB::InfiniteFuture,
            ) => AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                time,
                inclusivity,
                OpeningDirection::ToFuture,
            )),
            (
                StartB::Finite(AbsoluteFiniteBound {
                    time: start_time,
                    inclusivity: start_inclusivity,
                }),
                EndB::Finite(AbsoluteFiniteBound {
                    time: end_time,
                    inclusivity: end_inclusivity,
                }),
            ) => AbsoluteInterval::Bounded(BoundedAbsoluteInterval::unchecked_new_with_inclusivity(
                start_time,
                start_inclusivity,
                end_time,
                end_inclusivity,
            )),
        }
    }
}

/// Converts `(Option<Timestamp>, Option<Timestamp>)` into [`AbsoluteInterval`]
///
/// The first tuple element represents the start bound, the second element
/// represents the end bound.
impl From<(Option<Timestamp>, Option<Timestamp>)> for AbsoluteInterval {
    fn from((start_opt, end_opt): (Option<Timestamp>, Option<Timestamp>)) -> Self {
        match (start_opt, end_opt) {
            (Some(start), Some(end)) => AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(start, end)),
            (Some(start), None) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(start, OpeningDirection::ToFuture))
            },
            (None, Some(end)) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(end, OpeningDirection::ToPast))
            },
            (None, None) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(Option<(Timestamp, BoundInclusivity)>, Option<(Timestamp,
/// BoundInclusivity)>)` into [`AbsoluteInterval`]
///
/// The first tuple element represents the start bound, the second element
/// represents the end bound.
impl
    From<(
        Option<(Timestamp, BoundInclusivity)>,
        Option<(Timestamp, BoundInclusivity)>,
    )> for AbsoluteInterval
{
    fn from(
        (start_opt, end_opt): (
            Option<(Timestamp, BoundInclusivity)>,
            Option<(Timestamp, BoundInclusivity)>,
        ),
    ) -> Self {
        match (start_opt, end_opt) {
            (Some((start, start_inclusivity)), Some((end, end_inclusivity))) => AbsoluteInterval::Bounded(
                BoundedAbsoluteInterval::new_with_inclusivity(start, start_inclusivity, end, end_inclusivity),
            ),
            (Some((start, start_inclusivity)), None) => AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new_with_inclusivity(start, start_inclusivity, OpeningDirection::ToFuture),
            ),
            (None, Some((end, end_inclusivity))) => AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new_with_inclusivity(end, end_inclusivity, OpeningDirection::ToPast),
            ),
            (None, None) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbsoluteIntervalFromEmptiableAbsoluteBoundPairError;

impl Display for AbsoluteIntervalFromEmptiableAbsoluteBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Failed to convert the emptiable absolute bound pair into an absolute interval"
        )
    }
}

impl Error for AbsoluteIntervalFromEmptiableAbsoluteBoundPairError {}

impl TryFrom<EmptiableAbsoluteBoundPair> for AbsoluteInterval {
    type Error = AbsoluteIntervalFromEmptiableAbsoluteBoundPairError;

    fn try_from(value: EmptiableAbsoluteBoundPair) -> Result<Self, Self::Error> {
        type StartB = AbsoluteStartBound;
        type EndB = AbsoluteEndBound;

        match (value.partial_abs_start(), value.partial_abs_end()) {
            (None, _) | (_, None) => Err(AbsoluteIntervalFromEmptiableAbsoluteBoundPairError),
            (Some(StartB::InfinitePast), Some(EndB::InfiniteFuture)) => {
                Ok(AbsoluteInterval::Unbounded(UnboundedInterval))
            },
            (
                Some(StartB::InfinitePast),
                Some(EndB::Finite(AbsoluteFiniteBound {
                    time,
                    inclusivity,
                })),
            ) => Ok(AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new_with_inclusivity(time, inclusivity, OpeningDirection::ToPast),
            )),
            (
                Some(StartB::Finite(AbsoluteFiniteBound {
                    time,
                    inclusivity,
                })),
                Some(EndB::InfiniteFuture),
            ) => Ok(AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new_with_inclusivity(time, inclusivity, OpeningDirection::ToFuture),
            )),
            (
                Some(StartB::Finite(AbsoluteFiniteBound {
                    time: start_time,
                    inclusivity: start_inclusivity,
                })),
                Some(EndB::Finite(AbsoluteFiniteBound {
                    time: end_time,
                    inclusivity: end_inclusivity,
                })),
            ) => Ok(AbsoluteInterval::Bounded(
                BoundedAbsoluteInterval::unchecked_new_with_inclusivity(
                    start_time,
                    start_inclusivity,
                    end_time,
                    end_inclusivity,
                ),
            )),
        }
    }
}

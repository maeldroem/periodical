//! Relative interval
//!
//! Represents any form of specific relative intervals,
//! besides [`EmptyInterval`](crate::intervals::special::EmptyInterval).
//! That includes [`BoundedRelativeInterval`], [`HalfBoundedRelativeInterval`],
//! and [`UnboundedInterval`].
//!
//! The contained intervals conserve the [openness](Openness) invariant, but the
//! chosen variant can change. Compared to [`RelativeBoundPair`], thanks to the
//! variants we know exactly the kind of interval that is stored without needing
//! to check inner data.
//!
//! Usually this structure is for dealing with relative intervals as a single
//! type in a way that conserves the [openness](Openness) invariant, contrary to
//! [`RelativeBoundPair`].
//!
//! If you want to include
//! [`EmptyInterval`](crate::intervals::special::EmptyInterval) as a possible
//! variant,
//! see [`EmptiableRelativeInterval`](crate::intervals::relative::EmptiableRelativeInterval).

use std::cmp::Ordering;
use std::error::Error;
use std::fmt::Display;
use std::ops::{Bound, RangeBounds};

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
    HasDuration,
    HasOpenness,
    HasRelativity,
    Interval,
    OpeningDirection,
    Openness,
    Relativity,
};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeStartBound,
};
use crate::intervals::special::UnboundedInterval;

/// Relative interval
///
/// Represents any form of specific relative intervals,
/// besides [`EmptyInterval`](crate::intervals::special::EmptyInterval).
/// That includes [`BoundedRelativeInterval`], [`HalfBoundedRelativeInterval`],
/// and [`UnboundedInterval`].
///
/// The contained intervals conserve the [openness](Openness) invariant, but the
/// chosen variant can change. Compared to [`RelativeBoundPair`], thanks to the
/// variants we know exactly the kind of interval that is stored without needing
/// to check inner data.
///
/// Usually this structure is for dealing with relative intervals as a single
/// type in a way that conserves the [openness](Openness) invariant, contrary to
/// [`RelativeBoundPair`].
///
/// If you want to include
/// [`EmptyInterval`](crate::intervals::special::EmptyInterval) as a possible
/// variant,
/// see [`EmptiableRelativeInterval`](crate::intervals::relative::EmptiableRelativeInterval).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum RelativeInterval {
    Bounded(BoundedRelativeInterval),
    HalfBounded(HalfBoundedRelativeInterval),
    Unbounded(UnboundedInterval),
}

impl RelativeInterval {
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<SignedDuration>,
    {
        match (range.start_bound().cloned(), range.end_bound().cloned()) {
            (Bound::Included(start), Bound::Included(end)) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Inclusive,
                    end,
                    BoundInclusivity::Inclusive,
                ))
            },
            (Bound::Included(start), Bound::Excluded(end)) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Inclusive,
                    end,
                    BoundInclusivity::Exclusive,
                ))
            },
            (Bound::Excluded(start), Bound::Included(end)) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Exclusive,
                    end,
                    BoundInclusivity::Inclusive,
                ))
            },
            (Bound::Excluded(start), Bound::Excluded(end)) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Exclusive,
                    end,
                    BoundInclusivity::Exclusive,
                ))
            },
            (Bound::Included(start), Bound::Unbounded) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToFuture,
                ))
            },
            (Bound::Excluded(start), Bound::Unbounded) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                ))
            },
            (Bound::Unbounded, Bound::Included(start)) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToPast,
                ))
            },
            (Bound::Unbounded, Bound::Excluded(start)) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    start,
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                ))
            },
            (Bound::Unbounded, Bound::Unbounded) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }

    /// Compares two [`RelativeInterval`], but if they have the same start,
    /// order by decreasing length
    ///
    /// Uses [`EmptiableRelativeBoundPair::ord_by_start_and_inv_length`] under
    /// the hood.
    ///
    /// Don't rely on this method for checking for equality of start, as it will
    /// produce other [`Ordering`]s if their lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::RelativeInterval;
    /// # let mut bounds: [RelativeInterval; 0] = [];
    /// bounds.sort_by(RelativeInterval::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        self.rel_bound_pair()
            .ord_by_start_and_inv_length(&other.rel_bound_pair())
    }

    /// Wraps the interval in [`EmptiableRelativeInterval`]
    #[must_use]
    pub fn to_emptiable_interval(self) -> EmptiableRelativeInterval {
        EmptiableRelativeInterval::from(self)
    }
}

impl Interval for RelativeInterval {}

impl HasRelativeBoundPair for RelativeInterval {
    fn rel_bound_pair(&self) -> RelativeBoundPair {
        match self {
            Self::Bounded(bounded) => bounded.rel_bound_pair(),
            Self::HalfBounded(half_bounded) => half_bounded.rel_bound_pair(),
            Self::Unbounded(unbounded) => unbounded.rel_bound_pair(),
        }
    }

    fn rel_start(&self) -> RelativeStartBound {
        match self {
            Self::Bounded(bounded) => bounded.rel_start(),
            Self::HalfBounded(half_bounded) => half_bounded.rel_start(),
            Self::Unbounded(unbounded) => unbounded.rel_start(),
        }
    }

    fn rel_end(&self) -> RelativeEndBound {
        match self {
            Self::Bounded(bounded) => bounded.rel_end(),
            Self::HalfBounded(half_bounded) => half_bounded.rel_end(),
            Self::Unbounded(unbounded) => unbounded.rel_end(),
        }
    }
}

impl HasDuration for RelativeInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bounded(interval) => interval.duration(),
            Self::HalfBounded(interval) => interval.duration(),
            Self::Unbounded(interval) => interval.duration(),
        }
    }
}

impl HasRelativity for RelativeInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bounded(interval) => interval.relativity(),
            Self::HalfBounded(interval) => interval.relativity(),
            Self::Unbounded(interval) => interval.relativity(),
        }
    }
}

impl HasOpenness for RelativeInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Bounded(interval) => interval.openness(),
            Self::HalfBounded(interval) => interval.openness(),
            Self::Unbounded(interval) => interval.openness(),
        }
    }
}

impl PartialOrd for RelativeInterval {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeInterval {
    fn cmp(&self, other: &Self) -> Ordering {
        self.rel_bound_pair().cmp(&other.rel_bound_pair())
    }
}

impl From<BoundedRelativeInterval> for RelativeInterval {
    fn from(value: BoundedRelativeInterval) -> Self {
        RelativeInterval::Bounded(value)
    }
}

impl From<HalfBoundedRelativeInterval> for RelativeInterval {
    fn from(value: HalfBoundedRelativeInterval) -> Self {
        RelativeInterval::HalfBounded(value)
    }
}

impl From<UnboundedInterval> for RelativeInterval {
    fn from(value: UnboundedInterval) -> Self {
        RelativeInterval::Unbounded(value)
    }
}

impl From<RelativeBoundPair> for RelativeInterval {
    fn from(value: RelativeBoundPair) -> Self {
        type StartB = RelativeStartBound;
        type EndB = RelativeEndBound;

        match (value.rel_start(), value.rel_end()) {
            (StartB::InfinitePast, EndB::InfiniteFuture) => RelativeInterval::Unbounded(UnboundedInterval),
            (
                StartB::InfinitePast,
                EndB::Finite(RelativeFiniteBound {
                    offset,
                    inclusivity,
                }),
            ) => RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                offset,
                inclusivity,
                OpeningDirection::ToPast,
            )),
            (
                StartB::Finite(RelativeFiniteBound {
                    offset,
                    inclusivity,
                }),
                EndB::InfiniteFuture,
            ) => RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                offset,
                inclusivity,
                OpeningDirection::ToFuture,
            )),
            (
                StartB::Finite(RelativeFiniteBound {
                    offset: start_offset,
                    inclusivity: start_inclusivity,
                }),
                EndB::Finite(RelativeFiniteBound {
                    offset: end_offset,
                    inclusivity: end_inclusivity,
                }),
            ) => RelativeInterval::Bounded(BoundedRelativeInterval::unchecked_new_with_inclusivity(
                start_offset,
                start_inclusivity,
                end_offset,
                end_inclusivity,
            )),
        }
    }
}

/// Converts `(Option<SignedDuration>, Option<SignedDuration>)` into
/// [`RelativeInterval`]
///
/// The first tuple element represents the start bound, the second element
/// represents the end bound.
impl From<(Option<SignedDuration>, Option<SignedDuration>)> for RelativeInterval {
    fn from((start_opt, end_opt): (Option<SignedDuration>, Option<SignedDuration>)) -> Self {
        match (start_opt, end_opt) {
            (Some(start), Some(end)) => RelativeInterval::Bounded(BoundedRelativeInterval::new(start, end)),
            (Some(start), None) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(start, OpeningDirection::ToFuture))
            },
            (None, Some(end)) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(end, OpeningDirection::ToPast))
            },
            (None, None) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(Option<(SignedDuration, BoundInclusivity)>,
/// Option<(SignedDuration, BoundInclusivity)>)` into [`RelativeInterval`]
///
/// The first tuple element represents the start bound, the second element
/// represents the end bound.
impl
    From<(
        Option<(SignedDuration, BoundInclusivity)>,
        Option<(SignedDuration, BoundInclusivity)>,
    )> for RelativeInterval
{
    fn from(
        (start_opt, end_opt): (
            Option<(SignedDuration, BoundInclusivity)>,
            Option<(SignedDuration, BoundInclusivity)>,
        ),
    ) -> Self {
        match (start_opt, end_opt) {
            (Some((start, start_inclusivity)), Some((end, end_inclusivity))) => RelativeInterval::Bounded(
                BoundedRelativeInterval::new_with_inclusivity(start, start_inclusivity, end, end_inclusivity),
            ),
            (Some((start, start_inclusivity)), None) => RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(start, start_inclusivity, OpeningDirection::ToFuture),
            ),
            (None, Some((end, end_inclusivity))) => RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(end, end_inclusivity, OpeningDirection::ToPast),
            ),
            (None, None) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RelativeIntervalFromEmptiableRelativeBoundPairError;

impl Display for RelativeIntervalFromEmptiableRelativeBoundPairError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Failed to convert the emptiable relative bound pair into an relative interval"
        )
    }
}

impl Error for RelativeIntervalFromEmptiableRelativeBoundPairError {}

impl TryFrom<EmptiableRelativeBoundPair> for RelativeInterval {
    type Error = RelativeIntervalFromEmptiableRelativeBoundPairError;

    fn try_from(value: EmptiableRelativeBoundPair) -> Result<Self, Self::Error> {
        type StartB = RelativeStartBound;
        type EndB = RelativeEndBound;

        match (value.partial_rel_start(), value.partial_rel_end()) {
            (None, _) | (_, None) => Err(RelativeIntervalFromEmptiableRelativeBoundPairError),
            (Some(StartB::InfinitePast), Some(EndB::InfiniteFuture)) => {
                Ok(RelativeInterval::Unbounded(UnboundedInterval))
            },
            (
                Some(StartB::InfinitePast),
                Some(EndB::Finite(RelativeFiniteBound {
                    offset,
                    inclusivity,
                })),
            ) => Ok(RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(offset, inclusivity, OpeningDirection::ToPast),
            )),
            (
                Some(StartB::Finite(RelativeFiniteBound {
                    offset,
                    inclusivity,
                })),
                Some(EndB::InfiniteFuture),
            ) => Ok(RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(offset, inclusivity, OpeningDirection::ToFuture),
            )),
            (
                Some(StartB::Finite(RelativeFiniteBound {
                    offset: start_offset,
                    inclusivity: start_inclusivity,
                })),
                Some(EndB::Finite(RelativeFiniteBound {
                    offset: end_offset,
                    inclusivity: end_inclusivity,
                })),
            ) => Ok(RelativeInterval::Bounded(
                BoundedRelativeInterval::unchecked_new_with_inclusivity(
                    start_offset,
                    start_inclusivity,
                    end_offset,
                    end_inclusivity,
                ),
            )),
        }
    }
}

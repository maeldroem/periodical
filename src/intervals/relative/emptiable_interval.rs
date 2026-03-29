//! Relative emptiable interval
//!
//! Represents any form of specific relative intervals, including
//! [`EmptyInterval`]. That includes [`BoundedRelativeInterval`],
//! [`HalfBoundedRelativeInterval`], [`UnboundedInterval`],
//! and [`EmptyInterval`].
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
//! If you want to exclude [`EmptyInterval`] as a possible variant, see
//! [`RelativeInterval`].

use std::cmp::Ordering;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::SignedDuration;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

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
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeInterval,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum EmptiableRelativeInterval {
    Bounded(BoundedRelativeInterval),
    HalfBounded(HalfBoundedRelativeInterval),
    Unbounded(UnboundedInterval),
    Empty(EmptyInterval),
}

impl EmptiableRelativeInterval {
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
        self.emptiable_rel_bound_pair()
            .ord_by_start_and_inv_length(&other.emptiable_rel_bound_pair())
    }
}

impl Interval for EmptiableRelativeInterval {}

impl HasDuration for EmptiableRelativeInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bounded(interval) => interval.duration(),
            Self::HalfBounded(interval) => interval.duration(),
            Self::Unbounded(interval) => interval.duration(),
            Self::Empty(interval) => interval.duration(),
        }
    }
}

impl HasRelativity for EmptiableRelativeInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bounded(interval) => interval.relativity(),
            Self::HalfBounded(interval) => interval.relativity(),
            Self::Unbounded(interval) => interval.relativity(),
            Self::Empty(interval) => interval.relativity(),
        }
    }
}

impl HasOpenness for EmptiableRelativeInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Bounded(interval) => interval.openness(),
            Self::HalfBounded(interval) => interval.openness(),
            Self::Unbounded(interval) => interval.openness(),
            Self::Empty(interval) => interval.openness(),
        }
    }
}

impl HasEmptiableRelativeBoundPair for EmptiableRelativeInterval {
    fn emptiable_rel_bound_pair(&self) -> EmptiableRelativeBoundPair {
        match self {
            Self::Bounded(interval) => EmptiableRelativeBoundPair::from(interval.rel_bound_pair()),
            Self::HalfBounded(interval) => EmptiableRelativeBoundPair::from(interval.rel_bound_pair()),
            Self::Unbounded(interval) => EmptiableRelativeBoundPair::from(interval.rel_bound_pair()),
            Self::Empty(interval) => interval.emptiable_rel_bound_pair(),
        }
    }

    fn partial_rel_start(&self) -> Option<RelativeStartBound> {
        match self {
            Self::Bounded(interval) => interval.partial_rel_start(),
            Self::HalfBounded(interval) => interval.partial_rel_start(),
            Self::Unbounded(interval) => interval.partial_rel_start(),
            Self::Empty(interval) => interval.partial_rel_start(),
        }
    }

    fn partial_rel_end(&self) -> Option<RelativeEndBound> {
        match self {
            Self::Bounded(interval) => interval.partial_rel_end(),
            Self::HalfBounded(interval) => interval.partial_rel_end(),
            Self::Unbounded(interval) => interval.partial_rel_end(),
            Self::Empty(interval) => interval.partial_rel_end(),
        }
    }
}

impl Emptiable for EmptiableRelativeInterval {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty(_))
    }
}

impl PartialOrd for EmptiableRelativeInterval {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EmptiableRelativeInterval {
    fn cmp(&self, other: &Self) -> Ordering {
        self.emptiable_rel_bound_pair().cmp(&other.emptiable_rel_bound_pair())
    }
}

impl From<BoundedRelativeInterval> for EmptiableRelativeInterval {
    fn from(value: BoundedRelativeInterval) -> Self {
        EmptiableRelativeInterval::Bounded(value)
    }
}

impl From<HalfBoundedRelativeInterval> for EmptiableRelativeInterval {
    fn from(value: HalfBoundedRelativeInterval) -> Self {
        EmptiableRelativeInterval::HalfBounded(value)
    }
}

impl From<UnboundedInterval> for EmptiableRelativeInterval {
    fn from(value: UnboundedInterval) -> Self {
        EmptiableRelativeInterval::Unbounded(value)
    }
}

impl From<EmptyInterval> for EmptiableRelativeInterval {
    fn from(value: EmptyInterval) -> Self {
        EmptiableRelativeInterval::Empty(value)
    }
}

impl From<RelativeBoundPair> for EmptiableRelativeInterval {
    fn from(value: RelativeBoundPair) -> Self {
        type StartB = RelativeStartBound;
        type EndB = RelativeEndBound;

        match (value.rel_start(), value.rel_end()) {
            (StartB::InfinitePast, EndB::InfiniteFuture) => EmptiableRelativeInterval::Unbounded(UnboundedInterval),
            (
                StartB::InfinitePast,
                EndB::Finite(RelativeFiniteBound {
                    offset,
                    inclusivity,
                }),
            ) => EmptiableRelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
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
            ) => EmptiableRelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
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
            ) => EmptiableRelativeInterval::Bounded(BoundedRelativeInterval::unchecked_new_with_inclusivity(
                start_offset,
                start_inclusivity,
                end_offset,
                end_inclusivity,
            )),
        }
    }
}

impl From<EmptiableRelativeBoundPair> for EmptiableRelativeInterval {
    fn from(value: EmptiableRelativeBoundPair) -> Self {
        type StartB = RelativeStartBound;
        type EndB = RelativeEndBound;

        match (value.partial_rel_start(), value.partial_rel_end()) {
            (None, _) | (_, None) => EmptiableRelativeInterval::Empty(EmptyInterval),
            (Some(StartB::InfinitePast), Some(EndB::InfiniteFuture)) => {
                EmptiableRelativeInterval::Unbounded(UnboundedInterval)
            },
            (
                Some(StartB::InfinitePast),
                Some(EndB::Finite(RelativeFiniteBound {
                    offset,
                    inclusivity,
                })),
            ) => EmptiableRelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                offset,
                inclusivity,
                OpeningDirection::ToPast,
            )),
            (
                Some(StartB::Finite(RelativeFiniteBound {
                    offset,
                    inclusivity,
                })),
                Some(EndB::InfiniteFuture),
            ) => EmptiableRelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                offset,
                inclusivity,
                OpeningDirection::ToFuture,
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
            ) => EmptiableRelativeInterval::Bounded(BoundedRelativeInterval::unchecked_new_with_inclusivity(
                start_offset,
                start_inclusivity,
                end_offset,
                end_inclusivity,
            )),
        }
    }
}

impl From<RelativeInterval> for EmptiableRelativeInterval {
    fn from(value: RelativeInterval) -> Self {
        match value {
            RelativeInterval::Bounded(bounded) => EmptiableRelativeInterval::Bounded(bounded),
            RelativeInterval::HalfBounded(half_bounded) => EmptiableRelativeInterval::HalfBounded(half_bounded),
            RelativeInterval::Unbounded(unbounded) => EmptiableRelativeInterval::Unbounded(unbounded),
        }
    }
}

/// Converts `(Option<SignedDuration>, Option<SignedDuration>)` into
/// [`RelativeInterval`]
///
/// The first tuple element represents the start bound, the second element
/// represents the end bound.
impl From<(Option<SignedDuration>, Option<SignedDuration>)> for EmptiableRelativeInterval {
    fn from((from_opt, to_opt): (Option<SignedDuration>, Option<SignedDuration>)) -> Self {
        match (from_opt, to_opt) {
            (Some(from), Some(to)) => EmptiableRelativeInterval::Bounded(BoundedRelativeInterval::new(from, to)),
            (Some(from), None) => EmptiableRelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                from,
                OpeningDirection::ToFuture,
            )),
            (None, Some(to)) => {
                EmptiableRelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(to, OpeningDirection::ToPast))
            },
            (None, None) => EmptiableRelativeInterval::Unbounded(UnboundedInterval),
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
    )> for EmptiableRelativeInterval
{
    fn from(
        (start_opt, end_opt): (
            Option<(SignedDuration, BoundInclusivity)>,
            Option<(SignedDuration, BoundInclusivity)>,
        ),
    ) -> Self {
        match (start_opt, end_opt) {
            (Some((start, start_inclusivity)), Some((end, end_inclusivity))) => EmptiableRelativeInterval::Bounded(
                BoundedRelativeInterval::new_with_inclusivity(start, start_inclusivity, end, end_inclusivity),
            ),
            (Some((start, start_inclusivity)), None) => EmptiableRelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(start, start_inclusivity, OpeningDirection::ToFuture),
            ),
            (None, Some((end, end_inclusivity))) => EmptiableRelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(end, end_inclusivity, OpeningDirection::ToPast),
            ),
            (None, None) => EmptiableRelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(bool, Option<SignedDuration>, Option<SignedDuration>)` into
/// [`RelativeInterval`]
///
/// The second tuple element represents the start bound, the third element
/// represents the end bound.
///
/// The first boolean indicates whether the interval is an [`EmptyInterval`].
/// If it is set to `true`, the next elements are ignored altogether.
impl From<(bool, Option<SignedDuration>, Option<SignedDuration>)> for EmptiableRelativeInterval {
    fn from((is_empty, from_opt, to_opt): (bool, Option<SignedDuration>, Option<SignedDuration>)) -> Self {
        if is_empty {
            return EmptiableRelativeInterval::Empty(EmptyInterval);
        }

        match (from_opt, to_opt) {
            (Some(from), Some(to)) => EmptiableRelativeInterval::Bounded(BoundedRelativeInterval::new(from, to)),
            (Some(from), None) => EmptiableRelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(
                from,
                OpeningDirection::ToFuture,
            )),
            (None, Some(to)) => {
                EmptiableRelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(to, OpeningDirection::ToPast))
            },
            (None, None) => EmptiableRelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(bool, Option<(SignedDuration, BoundInclusivity)>,
/// Option<(SignedDuration, BoundInclusivity)>)` into [`RelativeInterval`]
///
/// The second tuple element represents the start bound, the third element
/// represents the end bound.
///
/// The first boolean indicates whether the interval is an [`EmptyInterval`].
/// If it is set to `true`, the next elements are ignored altogether.
impl
    From<(
        bool,
        Option<(SignedDuration, BoundInclusivity)>,
        Option<(SignedDuration, BoundInclusivity)>,
    )> for EmptiableRelativeInterval
{
    fn from(
        (is_empty, start_opt, end_opt): (
            bool,
            Option<(SignedDuration, BoundInclusivity)>,
            Option<(SignedDuration, BoundInclusivity)>,
        ),
    ) -> Self {
        if is_empty {
            return EmptiableRelativeInterval::Empty(EmptyInterval);
        }

        match (start_opt, end_opt) {
            (Some((start, start_inclusivity)), Some((end, end_inclusivity))) => EmptiableRelativeInterval::Bounded(
                BoundedRelativeInterval::new_with_inclusivity(start, start_inclusivity, end, end_inclusivity),
            ),
            (Some((start, start_inclusivity)), None) => EmptiableRelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(start, start_inclusivity, OpeningDirection::ToFuture),
            ),
            (None, Some((end, end_inclusivity))) => EmptiableRelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(end, end_inclusivity, OpeningDirection::ToPast),
            ),
            (None, None) => EmptiableRelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

impl From<()> for EmptiableRelativeInterval {
    fn from(_value: ()) -> Self {
        EmptiableRelativeInterval::Empty(EmptyInterval)
    }
}

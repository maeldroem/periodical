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
use std::ops::RangeBounds;

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
    HasDuration,
    HasOpenness,
    HasRelativity,
    Interval,
    IsEmpty,
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
    /// Creates an [`AbsoluteInterval`] from a [`Timestamp`] range
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{AbsoluteFiniteBound, AbsoluteInterval, HasAbsoluteBoundPair};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// let start = "2026-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end = "2026-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let interval = AbsoluteInterval::from_range(start..end);
    ///
    /// assert_eq!(
    ///     interval.abs_start(),
    ///     AbsoluteFiniteBound::new(start).to_start_bound(),
    /// );
    /// assert_eq!(
    ///     interval.abs_end(),
    ///     AbsoluteFiniteBound::new_with_inclusivity(end, BoundInclusivity::Exclusive).to_end_bound(),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn from_range<R>(range: R) -> Self
    where
        R: RangeBounds<Timestamp>,
    {
        Self::from(AbsoluteBoundPair::from_range(range))
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

    /// Returns the content of the [`Bounded`](AbsoluteInterval::Bounded) variant
    ///
    /// Consumes `self` and puts the content of the [`Bounded`](AbsoluteInterval::Bounded) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::BoundedAbsoluteInterval;
    /// let bounded_interval = BoundedAbsoluteInterval::new(
    ///     "2026-01-01 08:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    ///     "2026-01-01 16:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    /// );
    ///
    /// let interval = bounded_interval.clone().to_interval();
    ///
    /// assert_eq!(interval.bounded(), Some(bounded_interval));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn bounded(self) -> Option<BoundedAbsoluteInterval> {
        match self {
            Self::Bounded(interval) => Some(interval),
            _ => None,
        }
    }

    /// Returns the content of the [`HalfBounded`](AbsoluteInterval::HalfBounded) variant
    ///
    /// Consumes `self` and puts the content of the [`HalfBounded`](AbsoluteInterval::HalfBounded) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::HalfBoundedAbsoluteInterval;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// let half_bounded_interval = HalfBoundedAbsoluteInterval::new(
    ///     "2026-01-01 08:00:00[Europe/Oslo]"
    ///         .parse::<Zoned>()?
    ///         .timestamp(),
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// let interval = half_bounded_interval.clone().to_interval();
    ///
    /// assert_eq!(interval.half_bounded(), Some(half_bounded_interval));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn half_bounded(self) -> Option<HalfBoundedAbsoluteInterval> {
        match self {
            Self::HalfBounded(interval) => Some(interval),
            _ => None,
        }
    }

    /// Returns the content of the [`Unbounded`](AbsoluteInterval::Unbounded) variant
    ///
    /// Consumes `self` and puts the content of the [`Unbounded`](AbsoluteInterval::Unbounded) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::AbsoluteInterval;
    /// # use periodical::intervals::special::UnboundedInterval;
    /// let interval = AbsoluteInterval::Unbounded(UnboundedInterval);
    ///
    /// assert_eq!(interval.unbounded(), Some(UnboundedInterval));
    /// ```
    #[must_use]
    pub fn unbounded(self) -> Option<UnboundedInterval> {
        match self {
            Self::Unbounded(interval) => Some(interval),
            _ => None,
        }
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

impl IsEmpty for AbsoluteInterval {
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

/// Converts `(Option<(Timestamp, BoundInclusivity)>, Option<(Timestamp, BoundInclusivity)>)`
/// into [`AbsoluteInterval`]
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

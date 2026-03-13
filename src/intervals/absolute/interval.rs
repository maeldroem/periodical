
/// An absolute interval
///
/// An enumerator to store any kind of absolute interval: [`BoundedAbsoluteInterval`],
/// [`HalfBoundedAbsoluteInterval`], [`UnboundedInterval`], and [`EmptyInterval`].
///
/// The contained intervals conserve the [openness](Openness) invariant, but the chosen variant can change.
/// Compared to [`AbsoluteBounds`], thanks to the variants we know exactly the kind of interval that is stored
/// without needing to check inner data.
///
/// Usually this is the structure that you want to use when dealing with absolute intervals
/// as it has more conversion methods from standard types, and also provides a quick way to know the type of
/// the interval and perhaps extract from it to make its type immutable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum AbsoluteInterval {
    Bounded(BoundedAbsoluteInterval),
    HalfBounded(HalfBoundedAbsoluteInterval),
    Unbounded(UnboundedInterval),
    Empty(EmptyInterval),
}

impl AbsoluteInterval {
    /// Compares two [`AbsoluteInterval`], but if they have the same start, order by decreasing length
    ///
    /// Uses [`EmptiableAbsoluteBounds::ord_by_start_and_inv_length`] under the hood.
    ///
    /// Don't rely on this method for checking for equality of start, as it will produce other [`Ordering`]s if their
    /// lengths don't match too.
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
        self.emptiable_abs_bounds()
            .ord_by_start_and_inv_length(&other.emptiable_abs_bounds())
    }
}

impl Interval for AbsoluteInterval {}

impl HasDuration for AbsoluteInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bounded(interval) => interval.duration(),
            Self::HalfBounded(interval) => interval.duration(),
            Self::Unbounded(interval) => interval.duration(),
            Self::Empty(interval) => interval.duration(),
        }
    }
}

impl HasRelativity for AbsoluteInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bounded(interval) => interval.relativity(),
            Self::HalfBounded(interval) => interval.relativity(),
            Self::Unbounded(interval) => interval.relativity(),
            Self::Empty(interval) => interval.relativity(),
        }
    }
}

impl HasOpenness for AbsoluteInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Bounded(interval) => interval.openness(),
            Self::HalfBounded(interval) => interval.openness(),
            Self::Unbounded(interval) => interval.openness(),
            Self::Empty(interval) => interval.openness(),
        }
    }
}

impl HasEmptiableAbsoluteBounds for AbsoluteInterval {
    fn emptiable_abs_bounds(&self) -> EmptiableAbsoluteBounds {
        match self {
            Self::Bounded(interval) => EmptiableAbsoluteBounds::from(interval.abs_bounds()),
            Self::HalfBounded(interval) => EmptiableAbsoluteBounds::from(interval.abs_bounds()),
            Self::Unbounded(interval) => EmptiableAbsoluteBounds::from(interval.abs_bounds()),
            Self::Empty(interval) => interval.emptiable_abs_bounds(),
        }
    }

    fn partial_abs_start(&self) -> Option<AbsoluteStartBound> {
        match self {
            Self::Bounded(interval) => interval.partial_abs_start(),
            Self::HalfBounded(interval) => interval.partial_abs_start(),
            Self::Unbounded(interval) => interval.partial_abs_start(),
            Self::Empty(interval) => interval.partial_abs_start(),
        }
    }

    fn partial_abs_end(&self) -> Option<AbsoluteEndBound> {
        match self {
            Self::Bounded(interval) => interval.partial_abs_end(),
            Self::HalfBounded(interval) => interval.partial_abs_end(),
            Self::Unbounded(interval) => interval.partial_abs_end(),
            Self::Empty(interval) => interval.partial_abs_end(),
        }
    }
}

impl Emptiable for AbsoluteInterval {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty(_))
    }
}

impl PartialOrd for AbsoluteInterval {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteInterval {
    fn cmp(&self, other: &Self) -> Ordering {
        self.emptiable_abs_bounds().cmp(&other.emptiable_abs_bounds())
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

impl From<EmptyInterval> for AbsoluteInterval {
    fn from(value: EmptyInterval) -> Self {
        AbsoluteInterval::Empty(value)
    }
}

impl From<AbsoluteBounds> for AbsoluteInterval {
    fn from(value: AbsoluteBounds) -> Self {
        type StartB = AbsoluteStartBound;
        type EndB = AbsoluteEndBound;

        match (value.abs_start(), value.abs_end()) {
            (StartB::InfinitePast, EndB::InfiniteFuture) => AbsoluteInterval::Unbounded(UnboundedInterval),
            (StartB::InfinitePast, EndB::Finite(AbsoluteFiniteBound { time, inclusivity })) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    time,
                    inclusivity,
                    OpeningDirection::ToPast,
                ))
            },
            (StartB::Finite(AbsoluteFiniteBound { time, inclusivity }), EndB::InfiniteFuture) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    time,
                    inclusivity,
                    OpeningDirection::ToFuture,
                ))
            },
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

impl From<EmptiableAbsoluteBounds> for AbsoluteInterval {
    fn from(value: EmptiableAbsoluteBounds) -> Self {
        type StartB = AbsoluteStartBound;
        type EndB = AbsoluteEndBound;

        match (value.partial_abs_start(), value.partial_abs_end()) {
            (None, _) | (_, None) => AbsoluteInterval::Empty(EmptyInterval),
            (Some(StartB::InfinitePast), Some(EndB::InfiniteFuture)) => AbsoluteInterval::Unbounded(UnboundedInterval),
            (Some(StartB::InfinitePast), Some(EndB::Finite(AbsoluteFiniteBound { time, inclusivity }))) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    time,
                    inclusivity,
                    OpeningDirection::ToPast,
                ))
            },
            (Some(StartB::Finite(AbsoluteFiniteBound { time, inclusivity })), Some(EndB::InfiniteFuture)) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    time,
                    inclusivity,
                    OpeningDirection::ToFuture,
                ))
            },
            (
                Some(StartB::Finite(AbsoluteFiniteBound {
                    time: start_time,
                    inclusivity: start_inclusivity,
                })),
                Some(EndB::Finite(AbsoluteFiniteBound {
                    time: end_time,
                    inclusivity: end_inclusivity,
                })),
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
/// The first tuple element represents the start bound, the second element represents the end bound.
impl From<(Option<Timestamp>, Option<Timestamp>)> for AbsoluteInterval {
    fn from((from_opt, to_opt): (Option<Timestamp>, Option<Timestamp>)) -> Self {
        match (from_opt, to_opt) {
            (Some(from), Some(to)) => AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(from, to)),
            (Some(from), None) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(from, OpeningDirection::ToFuture))
            },
            (None, Some(to)) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(to, OpeningDirection::ToPast))
            },
            (None, None) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(Option<(Timestamp, BoundInclusivity)>, Option<(Timestamp, BoundInclusivity)>)`
/// into [`AbsoluteInterval`]
///
/// The first tuple element represents the start bound, the second element represents the end bound.
impl
    From<(
        Option<(Timestamp, BoundInclusivity)>,
        Option<(Timestamp, BoundInclusivity)>,
    )> for AbsoluteInterval
{
    fn from(
        (from_opt, to_opt): (
            Option<(Timestamp, BoundInclusivity)>,
            Option<(Timestamp, BoundInclusivity)>,
        ),
    ) -> Self {
        match (from_opt, to_opt) {
            (Some((from, from_inclusivity)), Some((to, to_inclusivity))) => AbsoluteInterval::Bounded(
                BoundedAbsoluteInterval::new_with_inclusivity(from, from_inclusivity, to, to_inclusivity),
            ),
            (Some((from, from_inclusivity)), None) => AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new_with_inclusivity(from, from_inclusivity, OpeningDirection::ToFuture),
            ),
            (None, Some((to, to_inclusivity))) => AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new_with_inclusivity(to, to_inclusivity, OpeningDirection::ToPast),
            ),
            (None, None) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(Option<(Timestamp, bool)>, Option<(Timestamp, bool)>)` into [`AbsoluteInterval`]
///
/// The first tuple element represents the start bound, the second element represents the end bound.
///
/// The booleans contained within the `Option<(Timestamp, bool)>`s are interpreted as _is it inclusive?_
impl From<(Option<(Timestamp, bool)>, Option<(Timestamp, bool)>)> for AbsoluteInterval {
    fn from((from_opt, to_opt): (Option<(Timestamp, bool)>, Option<(Timestamp, bool)>)) -> Self {
        match (from_opt, to_opt) {
            (Some((from, is_from_inclusive)), Some((to, is_to_inclusive))) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::from(is_from_inclusive),
                    to,
                    BoundInclusivity::from(is_to_inclusive),
                ))
            },
            (Some((from, is_from_inclusive)), None) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::from(is_from_inclusive),
                    OpeningDirection::ToFuture,
                ))
            },
            (None, Some((to, is_to_inclusive))) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    to,
                    BoundInclusivity::from(is_to_inclusive),
                    OpeningDirection::ToPast,
                ))
            },
            (None, None) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(bool, Option<Timestamp>, Option<Timestamp>)` into [`AbsoluteInterval`]
///
/// The second tuple element represents the start bound, the third element represents the end bound.
///
/// The first boolean indicates whether the interval is an [`EmptyInterval`].
/// If it is set to `true`, the next elements are ignored altogether.
impl From<(bool, Option<Timestamp>, Option<Timestamp>)> for AbsoluteInterval {
    fn from((is_empty, from_opt, to_opt): (bool, Option<Timestamp>, Option<Timestamp>)) -> Self {
        if is_empty {
            return AbsoluteInterval::Empty(EmptyInterval);
        }

        match (from_opt, to_opt) {
            (Some(from), Some(to)) => AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(from, to)),
            (Some(from), None) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(from, OpeningDirection::ToFuture))
            },
            (None, Some(to)) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(to, OpeningDirection::ToPast))
            },
            (None, None) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(bool, Option<(Timestamp, BoundInclusivity)>, Option<(Timestamp, BoundInclusivity)>)`
/// into [`AbsoluteInterval`]
///
/// The second tuple element represents the start bound, the third element represents the end bound.
///
/// The first boolean indicates whether the interval is an [`EmptyInterval`].
/// If it is set to `true`, the next elements are ignored altogether.
impl
    From<(
        bool,
        Option<(Timestamp, BoundInclusivity)>,
        Option<(Timestamp, BoundInclusivity)>,
    )> for AbsoluteInterval
{
    fn from(
        (is_empty, from_opt, to_opt): (
            bool,
            Option<(Timestamp, BoundInclusivity)>,
            Option<(Timestamp, BoundInclusivity)>,
        ),
    ) -> Self {
        if is_empty {
            return AbsoluteInterval::Empty(EmptyInterval);
        }

        match (from_opt, to_opt) {
            (Some((from, from_inclusivity)), Some((to, to_inclusivity))) => AbsoluteInterval::Bounded(
                BoundedAbsoluteInterval::new_with_inclusivity(from, from_inclusivity, to, to_inclusivity),
            ),
            (Some((from, from_inclusivity)), None) => AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new_with_inclusivity(from, from_inclusivity, OpeningDirection::ToFuture),
            ),
            (None, Some((to, to_inclusivity))) => AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new_with_inclusivity(to, to_inclusivity, OpeningDirection::ToPast),
            ),
            (None, None) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(bool, Option<(Timestamp, bool)>, Option<(Timestamp, bool)>)` into [`AbsoluteInterval`]
///
/// The second tuple element represents the start bound, the third element represents the end bound.
///
/// The first boolean indicates whether the interval is an [`EmptyInterval`].
/// If it is set to `true`, the next elements are ignored altogether.
///
/// The booleans contained within the `Option<(Timestamp, bool)>`s are interpreted as _is it inclusive?_
impl From<(bool, Option<(Timestamp, bool)>, Option<(Timestamp, bool)>)> for AbsoluteInterval {
    fn from(
        (is_empty, from_opt, to_opt): (bool, Option<(Timestamp, bool)>, Option<(Timestamp, bool)>),
    ) -> Self {
        if is_empty {
            return AbsoluteInterval::Empty(EmptyInterval);
        }

        match (from_opt, to_opt) {
            (Some((from, is_from_inclusive)), Some((to, is_to_inclusive))) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::from(is_from_inclusive),
                    to,
                    BoundInclusivity::from(is_to_inclusive),
                ))
            },
            (Some((from, is_from_inclusive)), None) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::from(is_from_inclusive),
                    OpeningDirection::ToFuture,
                ))
            },
            (None, Some((to, is_to_inclusive))) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    to,
                    BoundInclusivity::from(is_to_inclusive),
                    OpeningDirection::ToPast,
                ))
            },
            (None, None) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

// Unfortunately can't use impl<R: RangeBounds> From<R> as it's conflicting with the core implementation of From
/// Converts `(Bound<Timestamp>, Bound<Timestamp>)` into [`AbsoluteInterval`]
///
/// The first tuple element represents the start bound, the second tuple element represents the end bound.
impl From<(Bound<Timestamp>, Bound<Timestamp>)> for AbsoluteInterval {
    fn from((start_bound, end_bound): (Bound<Timestamp>, Bound<Timestamp>)) -> Self {
        match (start_bound, end_bound) {
            (Bound::Included(from), Bound::Included(to)) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    to,
                    BoundInclusivity::Inclusive,
                ))
            },
            (Bound::Included(from), Bound::Excluded(to)) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    to,
                    BoundInclusivity::Exclusive,
                ))
            },
            (Bound::Excluded(from), Bound::Included(to)) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    to,
                    BoundInclusivity::Inclusive,
                ))
            },
            (Bound::Excluded(from), Bound::Excluded(to)) => {
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    to,
                    BoundInclusivity::Exclusive,
                ))
            },
            (Bound::Included(from), Bound::Unbounded) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToFuture,
                ))
            },
            (Bound::Excluded(from), Bound::Unbounded) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                ))
            },
            (Bound::Unbounded, Bound::Included(from)) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToPast,
                ))
            },
            (Bound::Unbounded, Bound::Excluded(from)) => {
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                ))
            },
            (Bound::Unbounded, Bound::Unbounded) => AbsoluteInterval::Unbounded(UnboundedInterval),
        }
    }
}

impl From<Range<Timestamp>> for AbsoluteInterval {
    fn from(value: Range<Timestamp>) -> Self {
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::from(value))
    }
}

impl From<RangeInclusive<Timestamp>> for AbsoluteInterval {
    fn from(value: RangeInclusive<Timestamp>) -> Self {
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::from(value))
    }
}

impl From<RangeFrom<Timestamp>> for AbsoluteInterval {
    fn from(value: RangeFrom<Timestamp>) -> Self {
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::from(value))
    }
}

impl From<RangeTo<Timestamp>> for AbsoluteInterval {
    fn from(value: RangeTo<Timestamp>) -> Self {
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::from(value))
    }
}

impl From<RangeToInclusive<Timestamp>> for AbsoluteInterval {
    fn from(value: RangeToInclusive<Timestamp>) -> Self {
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::from(value))
    }
}

impl From<RangeFull> for AbsoluteInterval {
    fn from(_value: RangeFull) -> Self {
        AbsoluteInterval::Unbounded(UnboundedInterval)
    }
}

impl From<()> for AbsoluteInterval {
    fn from(_value: ()) -> Self {
        AbsoluteInterval::Empty(EmptyInterval)
    }
}

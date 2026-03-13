
/// A relative interval
///
/// An enumerator to store any kind of relative interval: [`BoundedRelativeInterval`],
/// [`HalfBoundedRelativeInterval`], [`UnboundedInterval`], and [`EmptyInterval`].
///
/// The contained intervals conserve the [openness](Openness) invariant, but the chosen variant can change.
/// Compared to [`RelativeBounds`], thanks to the variants we know exactly the kind of interval that is stored
/// without needing to check inner data.
///
/// Usually this is the structure that you want to use when dealing with relative intervals
/// as it has more conversion methods from standard types, and also provides a quick way to know the type of
/// the interval and perhaps extract from it to make its type immutable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum RelativeInterval {
    Bounded(BoundedRelativeInterval),
    HalfBounded(HalfBoundedRelativeInterval),
    Unbounded(UnboundedInterval),
    Empty(EmptyInterval),
}

impl RelativeInterval {
    /// Compares two [`RelativeInterval`], but if they have the same start, order by decreasing length
    ///
    /// Uses [`EmptiableRelativeBounds::ord_by_start_and_inv_length`] under the hood.
    ///
    /// Don't rely on this method for checking for equality of start, as it will produce other [`Ordering`]s if their
    /// lengths don't match too.
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
        self.emptiable_rel_bounds()
            .ord_by_start_and_inv_length(&other.emptiable_rel_bounds())
    }
}

impl Interval for RelativeInterval {}

impl HasDuration for RelativeInterval {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bounded(interval) => interval.duration(),
            Self::HalfBounded(interval) => interval.duration(),
            Self::Unbounded(interval) => interval.duration(),
            Self::Empty(interval) => interval.duration(),
        }
    }
}

impl HasRelativity for RelativeInterval {
    fn relativity(&self) -> Relativity {
        match self {
            Self::Bounded(interval) => interval.relativity(),
            Self::HalfBounded(interval) => interval.relativity(),
            Self::Unbounded(interval) => interval.relativity(),
            Self::Empty(interval) => interval.relativity(),
        }
    }
}

impl HasOpenness for RelativeInterval {
    fn openness(&self) -> Openness {
        match self {
            Self::Bounded(interval) => interval.openness(),
            Self::HalfBounded(interval) => interval.openness(),
            Self::Unbounded(interval) => interval.openness(),
            Self::Empty(interval) => interval.openness(),
        }
    }
}

impl HasEmptiableRelativeBounds for RelativeInterval {
    fn emptiable_rel_bounds(&self) -> EmptiableRelativeBounds {
        match self {
            Self::Bounded(interval) => EmptiableRelativeBounds::from(interval.rel_bounds()),
            Self::HalfBounded(interval) => EmptiableRelativeBounds::from(interval.rel_bounds()),
            Self::Unbounded(interval) => EmptiableRelativeBounds::from(interval.rel_bounds()),
            Self::Empty(interval) => interval.emptiable_rel_bounds(),
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

impl Emptiable for RelativeInterval {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty(_))
    }
}

impl PartialOrd for RelativeInterval {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeInterval {
    fn cmp(&self, other: &Self) -> Ordering {
        self.emptiable_rel_bounds().cmp(&other.emptiable_rel_bounds())
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

impl From<EmptyInterval> for RelativeInterval {
    fn from(value: EmptyInterval) -> Self {
        RelativeInterval::Empty(value)
    }
}

impl From<RelativeBounds> for RelativeInterval {
    fn from(value: RelativeBounds) -> Self {
        type StartB = RelativeStartBound;
        type EndB = RelativeEndBound;

        match (value.rel_start(), value.rel_end()) {
            (StartB::InfinitePast, EndB::InfiniteFuture) => RelativeInterval::Unbounded(UnboundedInterval),
            (StartB::InfinitePast, EndB::Finite(RelativeFiniteBound { offset, inclusivity })) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    offset,
                    inclusivity,
                    OpeningDirection::ToPast,
                ))
            },
            (StartB::Finite(RelativeFiniteBound { offset, inclusivity }), EndB::InfiniteFuture) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    offset,
                    inclusivity,
                    OpeningDirection::ToFuture,
                ))
            },
            (
                StartB::Finite(RelativeFiniteBound {
                    offset: start_offset,
                    inclusivity: start_inclusivity,
                }),
                EndB::Finite(RelativeFiniteBound {
                    offset: end_offset,
                    inclusivity: end_inclusivity,
                }),
            ) => RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                start_offset,
                start_inclusivity,
                end_offset - start_offset,
                end_inclusivity,
            )),
        }
    }
}

impl From<EmptiableRelativeBounds> for RelativeInterval {
    fn from(value: EmptiableRelativeBounds) -> Self {
        type StartB = RelativeStartBound;
        type EndB = RelativeEndBound;

        match (value.partial_rel_start(), value.partial_rel_end()) {
            (None, _) | (_, None) => RelativeInterval::Empty(EmptyInterval),
            (Some(StartB::InfinitePast), Some(EndB::InfiniteFuture)) => RelativeInterval::Unbounded(UnboundedInterval),
            (Some(StartB::InfinitePast), Some(EndB::Finite(RelativeFiniteBound { offset, inclusivity }))) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    offset,
                    inclusivity,
                    OpeningDirection::ToPast,
                ))
            },
            (Some(StartB::Finite(RelativeFiniteBound { offset, inclusivity })), Some(EndB::InfiniteFuture)) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    offset,
                    inclusivity,
                    OpeningDirection::ToFuture,
                ))
            },
            (
                Some(StartB::Finite(RelativeFiniteBound {
                    offset: start_offset,
                    inclusivity: start_inclusivity,
                })),
                Some(EndB::Finite(RelativeFiniteBound {
                    offset: end_offset,
                    inclusivity: end_inclusivity,
                })),
            ) => RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                start_offset,
                start_inclusivity,
                end_offset - start_offset,
                end_inclusivity,
            )),
        }
    }
}

/// Converts `(Option<SignedDuration>, Option<SignedDuration>)` into [`RelativeInterval`]
///
/// The first tuple element represents the start bound, the second element represents the end bound.
impl From<(Option<SignedDuration>, Option<SignedDuration>)> for RelativeInterval {
    fn from((from_opt, to_opt): (Option<SignedDuration>, Option<SignedDuration>)) -> Self {
        match (from_opt, to_opt) {
            (Some(from), Some(to)) => RelativeInterval::Bounded(BoundedRelativeInterval::new(from, to)),
            (Some(from), None) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(from, OpeningDirection::ToFuture))
            },
            (None, Some(to)) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(to, OpeningDirection::ToPast))
            },
            (None, None) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(Option<(SignedDuration, BoundInclusivity)>, Option<(SignedDuration, BoundInclusivity)>)`
/// into [`RelativeInterval`]
///
/// The first tuple element represents the start bound, the second element represents the end bound.
impl
    From<(
        Option<(SignedDuration, BoundInclusivity)>,
        Option<(SignedDuration, BoundInclusivity)>,
    )> for RelativeInterval
{
    fn from(
        (from_opt, to_opt): (
            Option<(SignedDuration, BoundInclusivity)>,
            Option<(SignedDuration, BoundInclusivity)>,
        ),
    ) -> Self {
        match (from_opt, to_opt) {
            (Some((from, from_inclusivity)), Some((to, to_inclusivity))) => RelativeInterval::Bounded(
                BoundedRelativeInterval::new_with_inclusivity(from, from_inclusivity, to, to_inclusivity),
            ),
            (Some((from, from_inclusivity)), None) => RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(from, from_inclusivity, OpeningDirection::ToFuture),
            ),
            (None, Some((to, to_inclusivity))) => RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(to, to_inclusivity, OpeningDirection::ToPast),
            ),
            (None, None) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(Option<(SignedDuration, bool)>, Option<(SignedDuration, bool)>)` into [`RelativeInterval`]
///
/// The first tuple element represents the start bound, the second element represents the end bound.
///
/// The booleans contained within the `Option<(SignedDuration, bool)>`s are interpreted as _is it inclusive?_
impl From<(Option<(SignedDuration, bool)>, Option<(SignedDuration, bool)>)> for RelativeInterval {
    fn from((from_opt, to_opt): (Option<(SignedDuration, bool)>, Option<(SignedDuration, bool)>)) -> Self {
        match (from_opt, to_opt) {
            (Some((from, is_from_inclusive)), Some((to, is_to_inclusive))) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::from(is_from_inclusive),
                    to,
                    BoundInclusivity::from(is_to_inclusive),
                ))
            },
            (Some((from, is_from_inclusive)), None) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::from(is_from_inclusive),
                    OpeningDirection::ToFuture,
                ))
            },
            (None, Some((to, is_to_inclusive))) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    to,
                    BoundInclusivity::from(is_to_inclusive),
                    OpeningDirection::ToPast,
                ))
            },
            (None, None) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(bool, Option<SignedDuration>, Option<SignedDuration>)` into [`RelativeInterval`]
///
/// The second tuple element represents the start bound, the third element represents the end bound.
///
/// The first boolean indicates whether the interval is an [`EmptyInterval`].
/// If it is set to `true`, the next elements are ignored altogether.
impl From<(bool, Option<SignedDuration>, Option<SignedDuration>)> for RelativeInterval {
    fn from((is_empty, from_opt, to_opt): (bool, Option<SignedDuration>, Option<SignedDuration>)) -> Self {
        if is_empty {
            return RelativeInterval::Empty(EmptyInterval);
        }

        match (from_opt, to_opt) {
            (Some(from), Some(to)) => RelativeInterval::Bounded(BoundedRelativeInterval::new(from, to)),
            (Some(from), None) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(from, OpeningDirection::ToFuture))
            },
            (None, Some(to)) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new(to, OpeningDirection::ToPast))
            },
            (None, None) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(bool, Option<(SignedDuration, BoundInclusivity)>, Option<(SignedDuration, BoundInclusivity)>)`
/// into [`RelativeInterval`]
///
/// The second tuple element represents the start bound, the third element represents the end bound.
///
/// The first boolean indicates whether the interval is an [`EmptyInterval`].
/// If it is set to `true`, the next elements are ignored altogether.
impl
    From<(
        bool,
        Option<(SignedDuration, BoundInclusivity)>,
        Option<(SignedDuration, BoundInclusivity)>,
    )> for RelativeInterval
{
    fn from(
        (is_empty, from_opt, to_opt): (
            bool,
            Option<(SignedDuration, BoundInclusivity)>,
            Option<(SignedDuration, BoundInclusivity)>,
        ),
    ) -> Self {
        if is_empty {
            return RelativeInterval::Empty(EmptyInterval);
        }

        match (from_opt, to_opt) {
            (Some((from, from_inclusivity)), Some((to, to_inclusivity))) => RelativeInterval::Bounded(
                BoundedRelativeInterval::new_with_inclusivity(from, from_inclusivity, to, to_inclusivity),
            ),
            (Some((from, from_inclusivity)), None) => RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(from, from_inclusivity, OpeningDirection::ToFuture),
            ),
            (None, Some((to, to_inclusivity))) => RelativeInterval::HalfBounded(
                HalfBoundedRelativeInterval::new_with_inclusivity(to, to_inclusivity, OpeningDirection::ToPast),
            ),
            (None, None) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

/// Converts `(bool, Option<(SignedDuration, bool)>, Option<(SignedDuration, bool)>)` into [`RelativeInterval`]
///
/// The second tuple element represents the start bound, the third element represents the end bound.
///
/// The first boolean indicates whether the interval is an [`EmptyInterval`].
/// If it is set to `true`, the next elements are ignored altogether.
///
/// The booleans contained within the `Option<(SignedDuration, bool)>`s are interpreted as _is it inclusive?_
impl From<(bool, Option<(SignedDuration, bool)>, Option<(SignedDuration, bool)>)> for RelativeInterval {
    fn from((is_empty, from_opt, to_opt): (bool, Option<(SignedDuration, bool)>, Option<(SignedDuration, bool)>)) -> Self {
        if is_empty {
            return RelativeInterval::Empty(EmptyInterval);
        }

        match (from_opt, to_opt) {
            (Some((from, is_from_inclusive)), Some((to, is_to_inclusive))) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::from(is_from_inclusive),
                    to,
                    BoundInclusivity::from(is_to_inclusive),
                ))
            },
            (Some((from, is_from_inclusive)), None) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::from(is_from_inclusive),
                    OpeningDirection::ToFuture,
                ))
            },
            (None, Some((to, is_to_inclusive))) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    to,
                    BoundInclusivity::from(is_to_inclusive),
                    OpeningDirection::ToPast,
                ))
            },
            (None, None) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

// Unfortunately can't use impl<R: RangeBounds> From<R> as it's conflicting with the core implementation of From
/// Converts `(Bound<SignedDuration>, Bound<SignedDuration>)` into [`RelativeInterval`]
///
/// The first tuple element represents the start bound, the second tuple element represents the end bound.
impl From<(Bound<SignedDuration>, Bound<SignedDuration>)> for RelativeInterval {
    fn from((start_bound, end_bound): (Bound<SignedDuration>, Bound<SignedDuration>)) -> Self {
        match (start_bound, end_bound) {
            (Bound::Included(from), Bound::Included(to)) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    to,
                    BoundInclusivity::Inclusive,
                ))
            },
            (Bound::Included(from), Bound::Excluded(to)) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    to,
                    BoundInclusivity::Exclusive,
                ))
            },
            (Bound::Excluded(from), Bound::Included(to)) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    to,
                    BoundInclusivity::Inclusive,
                ))
            },
            (Bound::Excluded(from), Bound::Excluded(to)) => {
                RelativeInterval::Bounded(BoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    to,
                    BoundInclusivity::Exclusive,
                ))
            },
            (Bound::Included(from), Bound::Unbounded) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToFuture,
                ))
            },
            (Bound::Excluded(from), Bound::Unbounded) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                ))
            },
            (Bound::Unbounded, Bound::Included(from)) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToPast,
                ))
            },
            (Bound::Unbounded, Bound::Excluded(from)) => {
                RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::new_with_inclusivity(
                    from,
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                ))
            },
            (Bound::Unbounded, Bound::Unbounded) => RelativeInterval::Unbounded(UnboundedInterval),
        }
    }
}

impl From<Range<SignedDuration>> for RelativeInterval {
    fn from(value: Range<SignedDuration>) -> Self {
        RelativeInterval::Bounded(BoundedRelativeInterval::from(value))
    }
}

impl From<RangeInclusive<SignedDuration>> for RelativeInterval {
    fn from(value: RangeInclusive<SignedDuration>) -> Self {
        RelativeInterval::Bounded(BoundedRelativeInterval::from(value))
    }
}

impl From<RangeFrom<SignedDuration>> for RelativeInterval {
    fn from(value: RangeFrom<SignedDuration>) -> Self {
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::from(value))
    }
}

impl From<RangeTo<SignedDuration>> for RelativeInterval {
    fn from(value: RangeTo<SignedDuration>) -> Self {
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::from(value))
    }
}

impl From<RangeToInclusive<SignedDuration>> for RelativeInterval {
    fn from(value: RangeToInclusive<SignedDuration>) -> Self {
        RelativeInterval::HalfBounded(HalfBoundedRelativeInterval::from(value))
    }
}

impl From<RangeFull> for RelativeInterval {
    fn from(_value: RangeFull) -> Self {
        RelativeInterval::Unbounded(UnboundedInterval)
    }
}

impl From<()> for RelativeInterval {
    fn from(_value: ()) -> Self {
        RelativeInterval::Empty(EmptyInterval)
    }
}

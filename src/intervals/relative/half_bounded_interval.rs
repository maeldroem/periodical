
/// A half-bounded relative interval
///
/// An interval with a set reference time and an [opening direction](OpeningDirection).
/// Like all specific relative interval types, it conserves the invariant of its bounds being
/// in chronological order[^chrono_order_invariant] and if the interval has a length of zero,
/// they must be inclusive[^doubly_inclusive_invariant].
///
/// However, like the other specific interval types, it conserves an additional invariant:
/// Its [openness](Openness) cannot change. That is to say a half-bounded interval must remain a half-bounded interval.
/// It cannot mutate from being a half-bounded interval to a bounded interval.
///
/// [^chrono_order_invariant]: This invariant is automatically guaranteed in this structure
///     since it only has one bound.
/// [^doubly_inclusive_invariant]: This invariant is automatically guaranteed in this structure
///     since the reference time is finite and therefore cannot reach the opposite end of the half-bounded interval,
///     since the opposite end is infinite.
///
/// Instead, if you are looking for a relative interval that doesn't keep the [openness](Openness) invariant,
/// see [`RelativeBounds`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct HalfBoundedRelativeInterval {
    reference_offset: SignedDuration,
    opening_direction: OpeningDirection,
    reference_inclusivity: BoundInclusivity,
}

impl HalfBoundedRelativeInterval {
    /// Creates a new [`HalfBoundedRelativeInterval`]
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let half_bounded_interval = HalfBoundedRelativeInterval::new(
    ///     Duration::hours(8),
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_offset(), Duration::hours(8));
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToPast);
    /// ```
    #[must_use]
    pub fn new(reference_offset: SignedDuration, opening_direction: OpeningDirection) -> Self {
        HalfBoundedRelativeInterval {
            reference_offset,
            opening_direction,
            reference_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new [`HalfBoundedRelativeInterval`] with the given bound inclusivities
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let half_bounded_interval = HalfBoundedRelativeInterval::new_with_inclusivity(
    ///     Duration::hours(8),
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_offset(), Duration::hours(8));
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToPast);
    /// ```
    #[must_use]
    pub fn new_with_inclusivity(
        reference_offset: SignedDuration,
        reference_time_inclusivity: BoundInclusivity,
        opening_direction: OpeningDirection,
    ) -> Self {
        HalfBoundedRelativeInterval {
            reference_offset,
            opening_direction,
            reference_inclusivity: reference_time_inclusivity,
        }
    }

    /// Returns the reference offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let half_bounded_interval = HalfBoundedRelativeInterval::new(
    ///     Duration::hours(8),
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_offset(), Duration::hours(8));
    /// ```
    #[must_use]
    pub fn reference_offset(&self) -> SignedDuration {
        self.reference_offset
    }

    /// Returns the opening direction
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let half_bounded_interval = HalfBoundedRelativeInterval::new(
    ///     Duration::hours(8),
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToPast);
    /// ```
    #[must_use]
    pub fn opening_direction(&self) -> OpeningDirection {
        self.opening_direction
    }

    /// Returns the inclusivity of the reference offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let half_bounded_interval = HalfBoundedRelativeInterval::new_with_inclusivity(
    ///     Duration::hours(8),
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    /// ```
    #[must_use]
    pub fn reference_inclusivity(&self) -> BoundInclusivity {
        self.reference_inclusivity
    }

    /// Sets the reference offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let mut half_bounded_interval = HalfBoundedRelativeInterval::new(
    ///     Duration::hours(8),
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// half_bounded_interval.set_offset(Duration::hours(1));
    ///
    /// assert_eq!(half_bounded_interval.reference_offset(), Duration::hours(1));
    /// ```
    pub fn set_offset(&mut self, new_offset: SignedDuration) {
        self.reference_offset = new_offset;
    }

    /// Sets the inclusivity of the reference offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::{BoundInclusivity, OpeningDirection};
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let mut half_bounded_interval = HalfBoundedRelativeInterval::new_with_inclusivity(
    ///     Duration::hours(8),
    ///     BoundInclusivity::Exclusive,
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// half_bounded_interval.set_reference_inclusivity(BoundInclusivity::Inclusive);
    ///
    /// assert_eq!(half_bounded_interval.reference_inclusivity(), BoundInclusivity::Inclusive);
    /// ```
    pub fn set_reference_inclusivity(&mut self, new_inclusivity: BoundInclusivity) {
        self.reference_inclusivity = new_inclusivity;
    }

    /// Sets the opening direction
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::OpeningDirection;
    /// # use periodical::intervals::relative::HalfBoundedRelativeInterval;
    /// let mut half_bounded_interval = HalfBoundedRelativeInterval::new(
    ///     Duration::hours(8),
    ///     OpeningDirection::ToPast,
    /// );
    ///
    /// half_bounded_interval.set_opening_direction(OpeningDirection::ToFuture);
    ///
    /// assert_eq!(half_bounded_interval.opening_direction(), OpeningDirection::ToFuture);
    /// ```
    pub fn set_opening_direction(&mut self, new_opening_direction: OpeningDirection) {
        self.opening_direction = new_opening_direction;
    }
}

impl Interval for HalfBoundedRelativeInterval {}

impl HasOpenness for HalfBoundedRelativeInterval {
    fn openness(&self) -> Openness {
        Openness::HalfBounded
    }
}

impl HasRelativity for HalfBoundedRelativeInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl HasDuration for HalfBoundedRelativeInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Infinite
    }
}

impl HasRelativeBounds for HalfBoundedRelativeInterval {
    fn rel_bounds(&self) -> RelativeBounds {
        RelativeBounds::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelativeStartBound {
        match self.opening_direction {
            OpeningDirection::ToPast => RelativeStartBound::InfinitePast,
            OpeningDirection::ToFuture => RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                self.reference_offset,
                self.reference_inclusivity,
            )),
        }
    }

    fn rel_end(&self) -> RelativeEndBound {
        match self.opening_direction {
            OpeningDirection::ToPast => RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                self.reference_offset,
                self.reference_inclusivity,
            )),
            OpeningDirection::ToFuture => RelativeEndBound::InfiniteFuture,
        }
    }
}

impl From<(SignedDuration, OpeningDirection)> for HalfBoundedRelativeInterval {
    fn from((offset, direction): (SignedDuration, OpeningDirection)) -> Self {
        HalfBoundedRelativeInterval::new(offset, direction)
    }
}

/// Converts `(SignedDuration, bool)` into [`HalfBoundedRelativeInterval`]
///
/// The boolean is interpreted as _is it going to future?_
impl From<(SignedDuration, bool)> for HalfBoundedRelativeInterval {
    fn from((offset, goes_to_future): (SignedDuration, bool)) -> Self {
        HalfBoundedRelativeInterval::new(offset, OpeningDirection::from(goes_to_future))
    }
}

impl From<((SignedDuration, BoundInclusivity), OpeningDirection)> for HalfBoundedRelativeInterval {
    fn from(((offset, inclusivity), direction): ((SignedDuration, BoundInclusivity), OpeningDirection)) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(offset, inclusivity, direction)
    }
}

/// Converts `((SignedDuration, BoundInclusivity), bool)` into [`HalfBoundedRelativeInterval`]
///
/// The boolean is interpreted as _is it going to future?_
impl From<((SignedDuration, BoundInclusivity), bool)> for HalfBoundedRelativeInterval {
    fn from(((offset, inclusivity), goes_to_future): ((SignedDuration, BoundInclusivity), bool)) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(offset, inclusivity, OpeningDirection::from(goes_to_future))
    }
}

/// Converts `((SignedDuration, bool), OpeningDirection)` into [`HalfBoundedRelativeInterval`]
///
/// The boolean is interpreted as _is it inclusive?_
impl From<((SignedDuration, bool), OpeningDirection)> for HalfBoundedRelativeInterval {
    fn from(((offset, is_inclusive), direction): ((SignedDuration, bool), OpeningDirection)) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(offset, BoundInclusivity::from(is_inclusive), direction)
    }
}

/// Converts `((SignedDuration, bool), bool)` into [`HalfBoundedRelativeInterval`]
///
/// The boolean of the first tuple element is interpreted as _is it inclusive?_
///
/// The boolean of the second tuple element is interpreted as _is it going to future?_
impl From<((SignedDuration, bool), bool)> for HalfBoundedRelativeInterval {
    fn from(((offset, is_inclusive), goes_to_future): ((SignedDuration, bool), bool)) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            offset,
            BoundInclusivity::from(is_inclusive),
            OpeningDirection::from(goes_to_future),
        )
    }
}

impl From<RangeFrom<SignedDuration>> for HalfBoundedRelativeInterval {
    fn from(range: RangeFrom<SignedDuration>) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    }
}

impl From<RangeTo<SignedDuration>> for HalfBoundedRelativeInterval {
    fn from(range: RangeTo<SignedDuration>) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            range.end,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    }
}

impl From<RangeToInclusive<SignedDuration>> for HalfBoundedRelativeInterval {
    fn from(range: RangeToInclusive<SignedDuration>) -> Self {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            range.end,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToPast,
        )
    }
}

/// Errors that can occur when trying to convert [`RelativeBounds`] into [`HalfBoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedRelativeIntervalFromRelativeBoundsError {
    NotHalfBoundedInterval,
}

impl Display for HalfBoundedRelativeIntervalFromRelativeBoundsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotHalfBoundedInterval => write!(f, "Not a half-bounded interval"),
        }
    }
}

impl Error for HalfBoundedRelativeIntervalFromRelativeBoundsError {}

impl TryFrom<RelativeBounds> for HalfBoundedRelativeInterval {
    type Error = HalfBoundedRelativeIntervalFromRelativeBoundsError;

    fn try_from(value: RelativeBounds) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (RelativeStartBound::InfinitePast, RelativeEndBound::Finite(finite_end)) => {
                Ok(HalfBoundedRelativeInterval::new_with_inclusivity(
                    finite_end.offset(),
                    finite_end.inclusivity(),
                    OpeningDirection::ToPast,
                ))
            },
            (RelativeStartBound::Finite(finite_start), RelativeEndBound::InfiniteFuture) => {
                Ok(HalfBoundedRelativeInterval::new_with_inclusivity(
                    finite_start.offset(),
                    finite_start.inclusivity(),
                    OpeningDirection::ToFuture,
                ))
            },
            _ => Err(Self::Error::NotHalfBoundedInterval),
        }
    }
}

/// Errors that can occur when trying to convert [`RelativeInterval`] into [`HalfBoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HalfBoundedRelativeIntervalFromRelativeIntervalError {
    WrongVariant,
}

impl Display for HalfBoundedRelativeIntervalFromRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for HalfBoundedRelativeIntervalFromRelativeIntervalError {}

impl TryFrom<RelativeInterval> for HalfBoundedRelativeInterval {
    type Error = HalfBoundedRelativeIntervalFromRelativeIntervalError;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::HalfBounded(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

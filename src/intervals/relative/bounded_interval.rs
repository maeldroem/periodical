
/// A bounded relative interval
///
/// An interval with a set offset and length. Like all specific relative interval types, it conserves the invariant
/// of its length cannot be negative, and if the length is 0, the bounds must be inclusive.
///
/// However, like the other specific interval types, it conserves an additional invariant:
/// Its [openness](Openness) cannot change. That is to say a bounded interval must remain a bounded interval.
/// It cannot mutate from being a bounded interval to a half-bounded interval.
///
/// Instead, if you are looking for a relative interval that doesn't keep the [openness](Openness) invariant,
/// see [`RelativeBounds`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct BoundedRelativeInterval {
    offset: SignedDuration,
    length: Duration,
    from_inclusivity: BoundInclusivity,
    to_inclusivity: BoundInclusivity,
}

impl BoundedRelativeInterval {
    /// Creates a new [`BoundedRelativeInterval`] without checking if it violates the invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let offset = Duration::hours(2);
    /// let length = Duration::hours(-5);
    ///
    /// // Even though the length is negative
    /// let bounded_interval = BoundedRelativeInterval::unchecked_new(offset, length);
    ///
    /// // It remains that way
    /// assert_eq!(bounded_interval.offset(), offset);
    /// assert_eq!(bounded_interval.length(), length);
    /// ```
    #[must_use]
    pub fn unchecked_new(offset: SignedDuration, length: Duration) -> Self {
        BoundedRelativeInterval {
            offset,
            length,
            from_inclusivity: BoundInclusivity::default(),
            to_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new [`BoundedRelativeInterval`] with default bound inclusivities
    ///
    /// If the length is negative, it assumes that the _end_ (offset + length) is the new offset,
    /// and that the absolute value of the length is the new length.
    ///
    /// # Panics
    ///
    /// Panics if the length is negative and `offset + length` underflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let offset = Duration::hours(1);
    /// let length = Duration::hours(-5);
    ///
    /// let bounded_interval = BoundedRelativeInterval::new(offset, length);
    ///
    /// assert_eq!(bounded_interval.offset(), Duration::hours(-4));
    /// assert_eq!(bounded_interval.length(), Duration::hours(5));
    /// ```
    #[must_use]
    pub fn new(mut offset: SignedDuration, mut length: Duration) -> Self {
        if length < Duration::zero() {
            offset += length;
            length = length.abs();
        }

        BoundedRelativeInterval {
            offset,
            length,
            from_inclusivity: BoundInclusivity::default(),
            to_inclusivity: BoundInclusivity::default(),
        }
    }

    /// Creates a new [`BoundedRelativeInterval`] with the given bound inclusivities without checking
    /// if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// // Length at 0, not doubly inclusive
    /// let bounded_interval = BoundedRelativeInterval::unchecked_new_with_inclusivity(
    ///     Duration::zero(),
    ///     BoundInclusivity::Inclusive,
    ///     Duration::zero(),
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(bounded_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(bounded_interval.to_inclusivity(), BoundInclusivity::Exclusive);
    /// ```
    #[must_use]
    pub fn unchecked_new_with_inclusivity(
        offset: SignedDuration,
        from_inclusivity: BoundInclusivity,
        length: Duration,
        to_inclusivity: BoundInclusivity,
    ) -> Self {
        BoundedRelativeInterval {
            offset,
            length,
            from_inclusivity,
            to_inclusivity,
        }
    }

    /// Creates a new [`BoundedRelativeInterval`] with the given bound inclusivities
    ///
    /// If the length is 0, then the inclusivities will be set to inclusive.
    ///
    /// If the length is negative, it assumes that the _end_ (offset + length) is the new offset,
    /// and that the absolute value of the length is the new length. The bound inclusivities are also swapped
    /// in this process.
    ///
    /// # Panics
    ///
    /// Panics if the length is negative and `offset + length` underflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// // Length at 0, not doubly inclusive
    /// let bounded_interval = BoundedRelativeInterval::new_with_inclusivity(
    ///     Duration::hours(-5),
    ///     BoundInclusivity::Inclusive,
    ///     Duration::zero(),
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// // Therefore gets reset to inclusive for both bounds
    /// assert_eq!(bounded_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// assert_eq!(bounded_interval.to_inclusivity(), BoundInclusivity::Inclusive);
    /// ```
    #[must_use]
    pub fn new_with_inclusivity(
        offset: SignedDuration,
        from_inclusivity: BoundInclusivity,
        length: Duration,
        to_inclusivity: BoundInclusivity,
    ) -> Self {
        match length.cmp(&Duration::zero()) {
            Ordering::Less => {
                Self::unchecked_new_with_inclusivity(offset + length, to_inclusivity, length.abs(), from_inclusivity)
            },
            Ordering::Equal => Self::unchecked_new(offset, length),
            Ordering::Greater => Self::unchecked_new_with_inclusivity(offset, from_inclusivity, length, to_inclusivity),
        }
    }

    /// Returns the offset of the interval
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let bounded_interval = BoundedRelativeInterval::new(
    ///     Duration::hours(1),
    ///     Duration::hours(5),
    /// );
    ///
    /// assert_eq!(bounded_interval.offset(), Duration::hours(1));
    /// ```
    #[must_use]
    pub fn offset(&self) -> SignedDuration {
        self.offset
    }

    /// Returns the length of the interval
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let bounded_interval = BoundedRelativeInterval::new(
    ///     Duration::hours(1),
    ///     Duration::hours(5),
    /// );
    ///
    /// assert_eq!(bounded_interval.length(), Duration::hours(5));
    /// ```
    #[must_use]
    pub fn length(&self) -> Duration {
        self.length
    }

    /// Returns the inclusivity of the start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let bounded_interval = BoundedRelativeInterval::new_with_inclusivity(
    ///     Duration::hours(1),
    ///     BoundInclusivity::Inclusive,
    ///     Duration::hours(5),
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(bounded_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// ```
    #[must_use]
    pub fn from_inclusivity(&self) -> BoundInclusivity {
        self.from_inclusivity
    }

    /// Returns the inclusivity of the end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let bounded_interval = BoundedRelativeInterval::new_with_inclusivity(
    ///     Duration::hours(1),
    ///     BoundInclusivity::Inclusive,
    ///     Duration::hours(5),
    ///     BoundInclusivity::Exclusive,
    /// );
    ///
    /// assert_eq!(bounded_interval.to_inclusivity(), BoundInclusivity::Exclusive);
    /// ```
    #[must_use]
    pub fn to_inclusivity(&self) -> BoundInclusivity {
        self.to_inclusivity
    }

    /// Sets the offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let mut bounded_interval = BoundedRelativeInterval::new(
    ///     Duration::hours(1),
    ///     Duration::hours(5),
    /// );
    ///
    /// bounded_interval.set_offset(Duration::hours(2));
    ///
    /// assert_eq!(bounded_interval.offset(), Duration::hours(2));
    /// ```
    pub fn set_offset(&mut self, new_offset: SignedDuration) {
        self.offset = new_offset;
    }

    /// Sets the length without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let mut bounded_interval = BoundedRelativeInterval::new(
    ///     Duration::hours(1),
    ///     Duration::hours(3),
    /// );
    ///
    /// // Negative length
    /// bounded_interval.unchecked_set_length(Duration::hours(-5));
    ///
    /// // Remains in the interval
    /// assert_eq!(bounded_interval.length(), Duration::hours(-5));
    /// ```
    pub fn unchecked_set_length(&mut self, new_length: Duration) {
        self.length = new_length;
    }

    /// Sets the length
    ///
    /// Returns whether the operation was successful and the length modified.
    /// If the given new length violates the invariants, the method simply returns `false`
    /// without changing the length.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let mut bounded_interval = BoundedRelativeInterval::new(
    ///     Duration::hours(1),
    ///     Duration::hours(3),
    /// );
    ///
    /// // New length is negative
    /// let was_successful = bounded_interval.set_length(Duration::hours(-5));
    ///
    /// // Therefore gets ignored
    /// assert!(!was_successful);
    /// assert_eq!(bounded_interval.length(), Duration::hours(3));
    /// ```
    pub fn set_length(&mut self, new_length: Duration) -> bool {
        match new_length.cmp(&Duration::zero()) {
            Ordering::Less => false,
            Ordering::Equal => {
                if self.from_inclusivity() != BoundInclusivity::Inclusive
                    || self.to_inclusivity() != BoundInclusivity::Inclusive
                {
                    return false;
                }

                self.unchecked_set_length(new_length);
                true
            },
            Ordering::Greater => {
                self.unchecked_set_length(new_length);
                true
            },
        }
    }

    /// Sets the inclusivity of the start bound
    ///
    /// Returns whether the operation was successful and the start bound's inclusivity modified.
    /// If the given new start bound inclusivity violates the invariants, the method simply returns `false`
    /// without changing the start bound's inclusivity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let mut bounded_interval = BoundedRelativeInterval::new(
    ///     Duration::hours(5),
    ///     Duration::zero(),
    /// );
    ///
    /// // Length is 0, therefore interval cannot be other than doubly inclusive
    /// let was_successful = bounded_interval.set_from_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// // Therefore the new inclusivity gets ignored
    /// assert!(!was_successful);
    /// assert_eq!(bounded_interval.from_inclusivity(), BoundInclusivity::Inclusive);
    /// ```
    pub fn set_from_inclusivity(&mut self, new_inclusivity: BoundInclusivity) -> bool {
        if self.length.is_zero() && new_inclusivity != BoundInclusivity::Inclusive {
            return false;
        }

        self.from_inclusivity = new_inclusivity;
        true
    }

    /// Sets the inclusivity of the end bound
    ///
    /// Returns whether the operation was successful and the end bound's inclusivity modified.
    /// If the given new end bound inclusivity violates the invariants, the method simply returns `false`
    /// without changing the end bound's inclusivity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::relative::BoundedRelativeInterval;
    /// let mut bounded_interval = BoundedRelativeInterval::new(
    ///     Duration::hours(5),
    ///     Duration::zero(),
    /// );
    ///
    /// // Length is 0, therefore interval cannot be other than doubly inclusive
    /// let was_successful = bounded_interval.set_to_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// // Therefore the new inclusivity gets ignored
    /// assert!(!was_successful);
    /// assert_eq!(bounded_interval.to_inclusivity(), BoundInclusivity::Inclusive);
    /// ```
    pub fn set_to_inclusivity(&mut self, new_inclusivity: BoundInclusivity) -> bool {
        if self.length.is_zero() && new_inclusivity != BoundInclusivity::Inclusive {
            return false;
        }

        self.to_inclusivity = new_inclusivity;
        true
    }
}

impl Interval for BoundedRelativeInterval {}

impl HasOpenness for BoundedRelativeInterval {
    fn openness(&self) -> Openness {
        Openness::Bounded
    }
}

impl HasRelativity for BoundedRelativeInterval {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl HasDuration for BoundedRelativeInterval {
    fn duration(&self) -> IntervalDuration {
        IntervalDuration::Finite(
            self.length,
            Epsilon::from((self.from_inclusivity(), self.to_inclusivity())),
        )
    }
}

impl HasRelativeBounds for BoundedRelativeInterval {
    fn rel_bounds(&self) -> RelativeBounds {
        RelativeBounds::new(self.rel_start(), self.rel_end())
    }

    fn rel_start(&self) -> RelativeStartBound {
        RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            self.offset,
            self.from_inclusivity,
        ))
    }

    fn rel_end(&self) -> RelativeEndBound {
        RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            self.offset + self.length,
            self.to_inclusivity,
        ))
    }
}

impl From<(SignedDuration, SignedDuration)> for BoundedRelativeInterval {
    fn from((from, to): (SignedDuration, SignedDuration)) -> Self {
        BoundedRelativeInterval::new(from, to)
    }
}

impl From<((SignedDuration, BoundInclusivity), (SignedDuration, BoundInclusivity))> for BoundedRelativeInterval {
    fn from(
        ((from, from_inclusivity), (to, to_inclusivity)): ((SignedDuration, BoundInclusivity), (SignedDuration, BoundInclusivity)),
    ) -> Self {
        BoundedRelativeInterval::new_with_inclusivity(from, from_inclusivity, to, to_inclusivity)
    }
}

/// Converts `((SignedDuration, bool), (SignedDuration, bool))` into [`BoundedRelativeInterval`]
///
/// The booleans in the original structure are to be interpreted as _is it inclusive?_
impl From<((SignedDuration, bool), (SignedDuration, bool))> for BoundedRelativeInterval {
    fn from(((from, is_from_inclusive), (to, is_to_inclusive)): ((SignedDuration, bool), (SignedDuration, bool))) -> Self {
        BoundedRelativeInterval::new_with_inclusivity(
            from,
            if is_from_inclusive {
                BoundInclusivity::Inclusive
            } else {
                BoundInclusivity::Exclusive
            },
            to,
            if is_to_inclusive {
                BoundInclusivity::Inclusive
            } else {
                BoundInclusivity::Exclusive
            },
        )
    }
}

impl From<Range<SignedDuration>> for BoundedRelativeInterval {
    fn from(range: Range<SignedDuration>) -> Self {
        BoundedRelativeInterval::new_with_inclusivity(
            range.start,
            BoundInclusivity::Inclusive,
            range.end,
            BoundInclusivity::Exclusive,
        )
    }
}

impl From<RangeInclusive<SignedDuration>> for BoundedRelativeInterval {
    fn from(range: RangeInclusive<SignedDuration>) -> Self {
        BoundedRelativeInterval::new_with_inclusivity(
            *range.start(),
            BoundInclusivity::Inclusive,
            *range.end(),
            BoundInclusivity::Inclusive,
        )
    }
}

/// Errors that can occur when trying to convert [`RelativeBounds`] into [`BoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedRelativeIntervalFromRelativeBoundsError {
    NotBoundedInterval,
}

impl Display for BoundedRelativeIntervalFromRelativeBoundsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotBoundedInterval => write!(f, "Not a bounded interval"),
        }
    }
}

impl Error for BoundedRelativeIntervalFromRelativeBoundsError {}

impl TryFrom<RelativeBounds> for BoundedRelativeInterval {
    type Error = BoundedRelativeIntervalFromRelativeBoundsError;

    fn try_from(value: RelativeBounds) -> Result<Self, Self::Error> {
        match (value.start(), value.end()) {
            (RelativeStartBound::Finite(finite_start), RelativeEndBound::Finite(finite_end)) => {
                Ok(BoundedRelativeInterval::new_with_inclusivity(
                    finite_start.offset(),
                    finite_start.inclusivity(),
                    finite_end.offset(),
                    finite_end.inclusivity(),
                ))
            },
            _ => Err(Self::Error::NotBoundedInterval),
        }
    }
}

/// Errors that can occur when trying to convert [`RelativeInterval`] into [`BoundedRelativeInterval`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundedRelativeIntervalFromRelativeIntervalError {
    WrongVariant,
}

impl Display for BoundedRelativeIntervalFromRelativeIntervalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongVariant => write!(f, "Wrong variant"),
        }
    }
}

impl Error for BoundedRelativeIntervalFromRelativeIntervalError {}

impl TryFrom<RelativeInterval> for BoundedRelativeInterval {
    type Error = BoundedRelativeIntervalFromRelativeIntervalError;

    fn try_from(value: RelativeInterval) -> Result<Self, Self::Error> {
        match value {
            RelativeInterval::Bounded(interval) => Ok(interval),
            _ => Err(Self::Error::WrongVariant),
        }
    }
}

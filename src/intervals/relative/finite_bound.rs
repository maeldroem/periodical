
/// A relative finite bound
///
/// Contains an offset [`SignedDuration`] and an ambiguous [`BoundInclusivity`]:
/// if it is [`Exclusive`](BoundInclusivity::Exclusive), then we additionally need the _source_
/// (whether it acts as the start or end of an interval) in order to know what this bound truly encompasses.
///
/// This is why when comparing finite bounds, only its position (for relative bounds, its offset) is used.
///
/// # Examples
///
/// ## Basic use
///
/// ```
/// # use chrono::Duration;
/// # use periodical::intervals::relative::RelativeFiniteBound;
/// let finite_bound = RelativeFiniteBound::new(Duration::hours(21));
/// ```
///
/// ## Creating an [`RelativeFiniteBound`] with an explicit [`BoundInclusivity`]
///
/// ```
/// # use chrono::Duration;
/// # use periodical::intervals::relative::RelativeFiniteBound;
/// # use periodical::intervals::meta::BoundInclusivity;
/// let finite_bound = RelativeFiniteBound::new_with_inclusivity(
///     Duration::hours(21),
///     BoundInclusivity::Exclusive,
/// );
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelativeFiniteBound {
    offset: SignedDuration,
    inclusivity: BoundInclusivity,
}

impl RelativeFiniteBound {
    /// Creates a new [`RelativeFiniteBound`] using the given offset
    ///
    /// This creates a finite bound using the [default `BoundInclusivity`](BoundInclusivity::default)
    #[must_use]
    pub fn new(offset: SignedDuration) -> Self {
        Self::new_with_inclusivity(offset, BoundInclusivity::default())
    }

    /// Creates a new [`RelativeFiniteBound`] using the given offset and [`BoundInclusivity`]
    #[must_use]
    pub fn new_with_inclusivity(offset: SignedDuration, inclusivity: BoundInclusivity) -> Self {
        RelativeFiniteBound { offset, inclusivity }
    }

    /// Returns the offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::SignedDuration;
    /// # use periodical::intervals::relative::RelativeFiniteBound;
    /// let finite_bound = RelativeFiniteBound::new(SignedDuration::hours(12));
    ///
    /// assert_eq!(finite_bound.offset(), SignedDuration::hours(12));
    /// ```
    #[must_use]
    pub fn offset(&self) -> SignedDuration {
        self.offset
    }

    /// Sets the offset
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::SignedDuration;
    /// # use periodical::intervals::relative::RelativeFiniteBound;
    /// let mut finite_bound = RelativeFiniteBound::new(SignedDuration::hours(1));
    /// finite_bound.set_offset(SignedDuration::hours(32));
    ///
    /// assert_eq!(finite_bound.offset(), SignedDuration::hours(32));
    /// ```
    pub fn set_offset(&mut self, offset: SignedDuration) {
        self.offset = offset;
    }

    /// Sets the inclusivity
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::SignedDuration;
    /// # use periodical::intervals::relative::RelativeFiniteBound;
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::prelude::*;
    /// let mut finite_bound = RelativeFiniteBound::new(SignedDuration::hours(1));
    /// finite_bound.set_inclusivity(BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(finite_bound.inclusivity(), BoundInclusivity::Exclusive);
    /// ```
    pub fn set_inclusivity(&mut self, inclusivity: BoundInclusivity) {
        self.inclusivity = inclusivity;
    }
}

impl HasBoundInclusivity for RelativeFiniteBound {
    fn inclusivity(&self) -> BoundInclusivity {
        self.inclusivity
    }
}

impl PartialOrd for RelativeFiniteBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeFiniteBound {
    fn cmp(&self, other: &Self) -> Ordering {
        self.offset.cmp(&other.offset)
    }
}

impl Display for RelativeFiniteBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Relative finite bound with offset {} ({})",
            self.offset, self.inclusivity
        )
    }
}

impl From<SignedDuration> for RelativeFiniteBound {
    fn from(value: SignedDuration) -> Self {
        RelativeFiniteBound::new(value)
    }
}

impl From<(SignedDuration, BoundInclusivity)> for RelativeFiniteBound {
    fn from((offset, inclusivity): (SignedDuration, BoundInclusivity)) -> Self {
        RelativeFiniteBound::new_with_inclusivity(offset, inclusivity)
    }
}

/// Conversion from the tuple `(SignedDuration, bool)` to [`RelativeFiniteBound`]
///
/// Interprets the boolean as _is it inclusive?_
impl From<(SignedDuration, bool)> for RelativeFiniteBound {
    fn from((offset, is_inclusive): (SignedDuration, bool)) -> Self {
        RelativeFiniteBound::new_with_inclusivity(
            offset,
            if is_inclusive {
                BoundInclusivity::Inclusive
            } else {
                BoundInclusivity::Exclusive
            },
        )
    }
}

/// Errors that can occur when trying to convert a [`Bound<SignedDuration>`] into an [`RelativeFiniteBound`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelativeFiniteBoundFromBoundError {
    /// The given bound was of the [`Unbounded`](Bound::Unbounded) variant
    IsUnbounded,
}

impl Display for RelativeFiniteBoundFromBoundError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IsUnbounded => {
                write!(
                    f,
                    "The given bound was of the `Unbounded` variant, \
                    and therefore could not be converted to an `RelativeFiniteBound`"
                )
            },
        }
    }
}

impl Error for RelativeFiniteBoundFromBoundError {}

impl TryFrom<Bound<SignedDuration>> for RelativeFiniteBound {
    type Error = RelativeFiniteBoundFromBoundError;

    fn try_from(value: Bound<SignedDuration>) -> Result<Self, Self::Error> {
        match value {
            Bound::Included(offset) => Ok(RelativeFiniteBound::new_with_inclusivity(
                offset,
                BoundInclusivity::Inclusive,
            )),
            Bound::Excluded(offset) => Ok(RelativeFiniteBound::new_with_inclusivity(
                offset,
                BoundInclusivity::Exclusive,
            )),
            Bound::Unbounded => Err(RelativeFiniteBoundFromBoundError::IsUnbounded),
        }
    }
}

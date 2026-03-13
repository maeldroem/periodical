
/// Possession of non-empty relative bounds
pub trait HasRelativeBounds {
    /// Returns the relative bounds of the object
    #[must_use]
    fn rel_bounds(&self) -> RelativeBounds;

    /// Returns the relative start bound of the object
    #[must_use]
    fn rel_start(&self) -> RelativeStartBound;

    /// Returns the relative end bound of the object
    #[must_use]
    fn rel_end(&self) -> RelativeEndBound;
}

/// Pair of [`RelativeStartBound`] and [`RelativeEndBound`]
///
/// This pair conserves the invariants required for an interval:
///
/// 1. The bounds are in chronological order
/// 2. If the bounds have the same offset, their inclusivities should be [inclusive] for both
///
/// [`RelativeBounds`] should be used when you want a non-empty interval which don't need to conserve
/// a given [`Openness`].
///
/// [inclusive]: BoundInclusivity::Inclusive
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct RelativeBounds {
    start: RelativeStartBound,
    end: RelativeEndBound,
}

impl RelativeBounds {
    /// Creates a new [`RelativeBounds`] without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
    /// # };
    /// // Start and end are not in chronological order!
    /// let start_offset = SignedDuration::hours(16);
    /// let end_offset = SignedDuration::hours(8);
    ///
    /// let start = RelativeStartBound::Finite(RelativeFiniteBound::new(start_offset));
    /// let end = RelativeEndBound::Finite(RelativeFiniteBound::new(end_offset));
    ///
    /// let bounds = RelativeBounds::unchecked_new(start, end);
    ///
    /// assert_eq!(bounds.start(), &start);
    /// assert_eq!(bounds.end(), &end);
    /// ```
    #[must_use]
    pub fn unchecked_new(start: RelativeStartBound, end: RelativeEndBound) -> Self {
        RelativeBounds { start, end }
    }

    /// Creates a new [`RelativeBounds`]
    ///
    /// Uses [`prepare_relative_bounds_for_interval_creation`] under the hood for making sure the bounds respect
    /// the invariants.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
    /// # };
    /// // Start and end are not in chronological order!
    /// let start_offset = SignedDuration::hours(16);
    /// let end_offset = SignedDuration::hours(8);
    ///
    /// let start = RelativeStartBound::Finite(RelativeFiniteBound::new(start_offset));
    /// let end = RelativeEndBound::Finite(RelativeFiniteBound::new(end_offset));
    ///
    /// let bounds = RelativeBounds::new(start, end);
    ///
    /// // Now the start and end are in chronological order
    /// assert_eq!(bounds.start(), &end);
    /// assert_eq!(bounds.end(), &start);
    /// ```
    #[must_use]
    pub fn new(mut start: RelativeStartBound, mut end: RelativeEndBound) -> Self {
        prepare_relative_bounds_for_interval_creation(&mut start, &mut end);
        Self::unchecked_new(start, end)
    }

    /// Returns the relative start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
    /// # };
    /// let start_offset = SignedDuration::hours(8);
    /// let end_offset = SignedDuration::hours(16);
    ///
    /// let start = RelativeStartBound::Finite(RelativeFiniteBound::new(start_offset));
    /// let end = RelativeEndBound::Finite(RelativeFiniteBound::new(end_offset));
    ///
    /// let bounds = RelativeBounds::new(start, end);
    ///
    /// assert_eq!(bounds.start(), &start);
    /// ```
    #[must_use]
    pub fn start(&self) -> &RelativeStartBound {
        &self.start
    }

    /// Returns the relative end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
    /// # };
    /// let start_offset = SignedDuration::hours(8);
    /// let end_offset = SignedDuration::hours(16);
    ///
    /// let start = RelativeStartBound::Finite(RelativeFiniteBound::new(start_offset));
    /// let end = RelativeEndBound::Finite(RelativeFiniteBound::new(end_offset));
    ///
    /// let bounds = RelativeBounds::new(start, end);
    ///
    /// assert_eq!(bounds.end(), &end);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn end(&self) -> &RelativeEndBound {
        &self.end
    }

    /// Sets the start bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
    /// # };
    /// let start_offset = SignedDuration::hours(8);
    /// let end_offset = SignedDuration::hours(16);
    ///
    /// let start = RelativeStartBound::Finite(RelativeFiniteBound::new(start_offset));
    /// let end = RelativeEndBound::Finite(RelativeFiniteBound::new(end_offset));
    ///
    /// let mut bounds = RelativeBounds::new(start, end);
    ///
    /// let new_start_offset = SignedDuration::hours(18);
    /// let new_start = RelativeStartBound::Finite(RelativeFiniteBound::new(new_start_offset));
    ///
    /// // New start is past the end
    /// bounds.unchecked_set_start(new_start);
    ///
    /// // And yet stays in `bounds`
    /// assert_eq!(bounds.start(), &new_start);
    /// assert_eq!(bounds.end(), &end);
    /// ```
    pub fn unchecked_set_start(&mut self, new_start: RelativeStartBound) {
        self.start = new_start;
    }

    /// Sets the end bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::relative::{
    /// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
    /// # };
    /// let start_offset = Duration::hours(8);
    /// let end_offset = Duration::hours(16);
    ///
    /// let start = RelativeStartBound::Finite(RelativeFiniteBound::new(start_offset));
    /// let end = RelativeEndBound::Finite(RelativeFiniteBound::new(end_offset));
    ///
    /// let mut bounds = RelativeBounds::new(start, end);
    ///
    /// let new_end_offset = Duration::hours(6);
    /// let new_end = RelativeEndBound::Finite(RelativeFiniteBound::new(new_end_offset));
    ///
    /// // New end is before the start
    /// bounds.unchecked_set_end(new_end);
    ///
    /// // And yet stays in `bounds`
    /// assert_eq!(bounds.start(), &start);
    /// assert_eq!(bounds.end(), &new_end);
    /// ```
    pub fn unchecked_set_end(&mut self, new_end: RelativeEndBound) {
        self.end = new_end;
    }

    /// Sets the start bound
    ///
    /// Returns whether the operation was successful and the start bound modified.
    /// If the given new start bound violates the invariants, the method simply returns `false`
    /// without changing the start bound.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::relative::{
    /// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
    /// # };
    /// let start_offset = Duration::hours(8);
    /// let end_offset = Duration::hours(16);
    ///
    /// let start = RelativeStartBound::Finite(RelativeFiniteBound::new(start_offset));
    /// let end = RelativeEndBound::Finite(RelativeFiniteBound::new(end_offset));
    ///
    /// let mut bounds = RelativeBounds::new(start, end);
    ///
    /// let new_start_offset = Duration::hours(18);
    /// let new_start = RelativeStartBound::Finite(RelativeFiniteBound::new(new_start_offset));
    ///
    /// // New start is past the end, and therefore gets ignored
    /// let was_successful = bounds.set_start(new_start);
    ///
    /// assert!(!was_successful);
    /// assert_eq!(bounds.start(), &start);
    /// assert_eq!(bounds.end(), &end);
    /// ```
    pub fn set_start(&mut self, new_start: RelativeStartBound) -> bool {
        match check_relative_bounds_for_interval_creation(&new_start, self.end()) {
            Ok(()) => {
                self.unchecked_set_start(new_start);
                true
            },
            Err(_) => false,
        }
    }

    /// Sets the end bound
    ///
    /// Returns whether the operation was successful and the end bound modified.
    /// If the given new end bound violates the invariants, the method simply returns `false`
    /// without changing the end bound.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::Duration;
    /// # use periodical::intervals::relative::{
    /// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
    /// # };
    /// let start_offset = Duration::hours(8);
    /// let end_offset = Duration::hours(16);
    ///
    /// let start = RelativeStartBound::Finite(RelativeFiniteBound::new(start_offset));
    /// let end = RelativeEndBound::Finite(RelativeFiniteBound::new(end_offset));
    ///
    /// let mut bounds = RelativeBounds::new(start, end);
    ///
    /// let new_end_offset = Duration::hours(6);
    /// let new_end = RelativeEndBound::Finite(RelativeFiniteBound::new(new_end_offset));
    ///
    /// // New end is before the start, and therefore gets ignored
    /// let was_successful = bounds.set_end(new_end);
    ///
    /// assert!(!was_successful);
    /// assert_eq!(bounds.start(), &start);
    /// assert_eq!(bounds.end(), &end);
    /// ```
    pub fn set_end(&mut self, new_end: RelativeEndBound) -> bool {
        match check_relative_bounds_for_interval_creation(self.start(), &new_end) {
            Ok(()) => {
                self.unchecked_set_end(new_end);
                true
            },
            Err(_) => false,
        }
    }

    /// Compares two [`RelativeBounds`], but if they have the same start, order by decreasing length
    ///
    /// Don't rely on this method for checking for equality of start, as it will produce other [`Ordering`]s if their
    /// lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::RelativeBounds;
    /// # let mut bounds: [RelativeBounds; 0] = [];
    /// bounds.sort_by(RelativeBounds::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        match self.cmp(other) {
            Ordering::Less => Ordering::Less,
            Ordering::Equal => self.end.cmp(&other.end).reverse(),
            Ordering::Greater => Ordering::Greater,
        }
    }
}

impl Interval for RelativeBounds {}

impl HasRelativeBounds for RelativeBounds {
    fn rel_bounds(&self) -> RelativeBounds {
        self.clone()
    }

    fn rel_start(&self) -> RelativeStartBound {
        *self.start()
    }

    fn rel_end(&self) -> RelativeEndBound {
        *self.end()
    }
}

impl HasDuration for RelativeBounds {
    fn duration(&self) -> IntervalDuration {
        match (self.start(), self.end()) {
            (RelativeStartBound::InfinitePast, _) | (_, RelativeEndBound::InfiniteFuture) => IntervalDuration::Infinite,
            (RelativeStartBound::Finite(finite_start), RelativeEndBound::Finite(finite_end)) => {
                IntervalDuration::Finite(
                    finite_end
                        .offset()
                        .checked_sub(&finite_start.offset())
                        .unwrap_or(SignedDuration::zero()),
                    Epsilon::from((finite_start.inclusivity(), finite_end.inclusivity())),
                )
            },
        }
    }
}

impl HasOpenness for RelativeBounds {
    fn openness(&self) -> Openness {
        match (self.start(), self.end()) {
            (RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture) => Openness::Unbounded,
            (RelativeStartBound::InfinitePast, RelativeEndBound::Finite(_))
            | (RelativeStartBound::Finite(_), RelativeEndBound::InfiniteFuture) => Openness::HalfBounded,
            (RelativeStartBound::Finite(_), RelativeEndBound::Finite(_)) => Openness::Bounded,
        }
    }
}

impl HasRelativity for RelativeBounds {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl PartialOrd for RelativeBounds {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeBounds {
    fn cmp(&self, other: &Self) -> Ordering {
        // using the comparison of self.end and other.end as a way to disambiguate when the two starts are equal
        // leads to side-effects, like when we store absolute bounds inside a BTreeSet, then if we use `range()`,
        // one can be considered out of the range when it shouldn't.
        self.start.cmp(&other.start)
    }
}

impl Display for RelativeBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = Ok(());

        result = result.and(write!(f, "Relative bounds: "));

        match self.start() {
            RelativeStartBound::Finite(RelativeFiniteBound { offset, inclusivity }) => {
                result = result.and(write!(f, "{offset} ({inclusivity})"));
            },
            RelativeStartBound::InfinitePast => {
                result = result.and(write!(f, "Infinite past"));
            },
        }

        result = result.and(write!(f, " to "));

        match self.end() {
            RelativeEndBound::Finite(RelativeFiniteBound { offset, inclusivity }) => {
                result = result.and(write!(f, "{offset} ({inclusivity})"));
            },
            RelativeEndBound::InfiniteFuture => {
                result = result.and(write!(f, "Infinite future"));
            },
        }

        result
    }
}

impl<R> From<R> for RelativeBounds
where
    R: RangeBounds<SignedDuration>,
{
    fn from(range: R) -> Self {
        RelativeBounds::new(
            RelativeStartBound::from(range.start_bound().cloned()),
            RelativeEndBound::from(range.end_bound().cloned()),
        )
    }
}

/// Errors that can occur when trying to convert [`EmptiableRelativeBounds`] into [`RelativeBounds`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelativeBoundsFromEmptiableRelativeBoundsError {
    EmptyVariant,
}

impl Display for RelativeBoundsFromEmptiableRelativeBoundsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyVariant => write!(f, "Provided EmptiableRelativeBounds was empty"),
        }
    }
}

impl Error for RelativeBoundsFromEmptiableRelativeBoundsError {}

impl TryFrom<EmptiableRelativeBounds> for RelativeBounds {
    type Error = RelativeBoundsFromEmptiableRelativeBoundsError;

    fn try_from(value: EmptiableRelativeBounds) -> Result<Self, Self::Error> {
        match value {
            EmptiableRelativeBounds::Empty => Err(RelativeBoundsFromEmptiableRelativeBoundsError::EmptyVariant),
            EmptiableRelativeBounds::Bound(bounds) => Ok(bounds),
        }
    }
}


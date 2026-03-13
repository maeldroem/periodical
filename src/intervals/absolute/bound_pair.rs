
/// Possession of **non-empty** absolute bounds
pub trait HasAbsoluteBounds {
    /// Returns the absolute bounds of the object
    #[must_use]
    fn abs_bounds(&self) -> AbsoluteBounds;

    /// Returns the absolute start bound of the object
    #[must_use]
    fn abs_start(&self) -> AbsoluteStartBound;

    /// Returns the absolute end bound of the object
    #[must_use]
    fn abs_end(&self) -> AbsoluteEndBound;
}

/// Pair of [`AbsoluteStartBound`] and [`AbsoluteEndBound`]
///
/// This pair conserves the invariants required for an interval:
///
/// 1. The bounds are in chronological order
/// 2. If the bounds have the same time, their inclusivities should be [inclusive] for both
///
/// [`AbsoluteBounds`] should be used when you want a non-empty interval which don't need to conserve
/// a given [`Openness`].
///
/// [inclusive]: BoundInclusivity::Inclusive
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct AbsoluteBounds {
    start: AbsoluteStartBound,
    end: AbsoluteEndBound,
}

impl AbsoluteBounds {
    /// Creates a new [`AbsoluteBounds`] without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// // Start and end are not in chronological order!
    /// let start_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let bounds = AbsoluteBounds::unchecked_new(start, end);
    ///
    /// assert_eq!(bounds.start(), &start);
    /// assert_eq!(bounds.end(), &end);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn unchecked_new(start: AbsoluteStartBound, end: AbsoluteEndBound) -> Self {
        AbsoluteBounds { start, end }
    }

    /// Creates a new [`AbsoluteBounds`]
    ///
    /// Uses [`prepare_absolute_bounds_for_interval_creation`] under the hood for making sure the bounds respect
    /// the invariants.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// // Start and end are not in chronological order!
    /// let start_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let bounds = AbsoluteBounds::new(start, end);
    ///
    /// // Now the start and end are in chronological order
    /// assert_eq!(bounds.start(), &end);
    /// assert_eq!(bounds.end(), &start);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn new(mut start: AbsoluteStartBound, mut end: AbsoluteEndBound) -> Self {
        prepare_absolute_bounds_for_interval_creation(&mut start, &mut end);
        Self::unchecked_new(start, end)
    }

    /// Returns the absolute start bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let bounds = AbsoluteBounds::new(start, end);
    ///
    /// assert_eq!(bounds.start(), &start);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn start(&self) -> &AbsoluteStartBound {
        &self.start
    }

    /// Returns the absolute end bound
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let bounds = AbsoluteBounds::new(start, end);
    ///
    /// assert_eq!(bounds.end(), &end);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn end(&self) -> &AbsoluteEndBound {
        &self.end
    }

    /// Sets the start bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let mut bounds = AbsoluteBounds::new(start, end);
    ///
    /// let new_start_time = "2025-01-01 18:00:00Z".parse::<Timestamp>()?;
    /// let new_start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(new_start_time));
    ///
    /// // New start is past the end
    /// bounds.unchecked_set_start(new_start);
    ///
    /// // And yet stays in `bounds`
    /// assert_eq!(bounds.start(), &new_start);
    /// assert_eq!(bounds.end(), &end);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn unchecked_set_start(&mut self, new_start: AbsoluteStartBound) {
        self.start = new_start;
    }

    /// Sets the end bound without checking if it violates invariants
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let mut bounds = AbsoluteBounds::new(start, end);
    ///
    /// let new_end_time = "2025-01-01 06:00:00Z".parse::<Timestamp>()?;
    /// let new_end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(new_end_time));
    ///
    /// // New end is before the start
    /// bounds.unchecked_set_end(new_end);
    ///
    /// // And yet stays in `bounds`
    /// assert_eq!(bounds.start(), &start);
    /// assert_eq!(bounds.end(), &new_end);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn unchecked_set_end(&mut self, new_end: AbsoluteEndBound) {
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
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let mut bounds = AbsoluteBounds::new(start, end);
    ///
    /// let new_start_time = "2025-01-01 18:00:00Z".parse::<Timestamp>()?;
    /// let new_start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(new_start_time));
    ///
    /// // New start is past the end, and therefore gets ignored
    /// let was_successful = bounds.set_start(new_start);
    ///
    /// assert!(!was_successful);
    /// assert_eq!(bounds.start(), &start);
    /// assert_eq!(bounds.end(), &end);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_start(&mut self, new_start: AbsoluteStartBound) -> bool {
        match check_absolute_bounds_for_interval_creation(&new_start, self.end()) {
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
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// let start_time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let end_time = "2025-01-01 16:00:00Z".parse::<Timestamp>()?;
    ///
    /// let start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(start_time));
    /// let end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(end_time));
    ///
    /// let mut bounds = AbsoluteBounds::new(start, end);
    ///
    /// let new_end_time = "2025-01-01 06:00:00Z".parse::<Timestamp>()?;
    /// let new_end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(new_end_time));
    ///
    /// // New end is before the start, and therefore gets ignored
    /// let was_successful = bounds.set_end(new_end);
    ///
    /// assert!(!was_successful);
    /// assert_eq!(bounds.start(), &start);
    /// assert_eq!(bounds.end(), &end);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    pub fn set_end(&mut self, new_end: AbsoluteEndBound) -> bool {
        match check_absolute_bounds_for_interval_creation(self.start(), &new_end) {
            Ok(()) => {
                self.unchecked_set_end(new_end);
                true
            },
            Err(_) => false,
        }
    }

    /// Compares two [`AbsoluteBounds`], but if they have the same start, order by decreasing length
    ///
    /// Don't rely on this method for checking for equality of start, as it will produce other [`Ordering`]s if their
    /// lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::AbsoluteBounds;
    /// # let mut bounds: [AbsoluteBounds; 0] = [];
    /// bounds.sort_by(AbsoluteBounds::ord_by_start_and_inv_length);
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

impl Interval for AbsoluteBounds {}

impl HasAbsoluteBounds for AbsoluteBounds {
    fn abs_bounds(&self) -> AbsoluteBounds {
        self.clone()
    }

    fn abs_start(&self) -> AbsoluteStartBound {
        *self.start()
    }

    fn abs_end(&self) -> AbsoluteEndBound {
        *self.end()
    }
}

impl HasDuration for AbsoluteBounds {
    fn duration(&self) -> IntervalDuration {
        match (self.start(), self.end()) {
            (AbsoluteStartBound::InfinitePast, _) | (_, AbsoluteEndBound::InfiniteFuture) => IntervalDuration::Infinite,
            (AbsoluteStartBound::Finite(finite_start), AbsoluteEndBound::Finite(finite_end)) => {
                IntervalDuration::Finite(
                    finite_end.time().signed_duration_since(finite_start.time()),
                    Epsilon::from((finite_start.inclusivity(), finite_end.inclusivity())),
                )
            },
        }
    }
}

impl HasOpenness for AbsoluteBounds {
    fn openness(&self) -> Openness {
        match (self.start(), self.end()) {
            (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture) => Openness::Unbounded,
            (AbsoluteStartBound::InfinitePast, AbsoluteEndBound::Finite(_))
            | (AbsoluteStartBound::Finite(_), AbsoluteEndBound::InfiniteFuture) => Openness::HalfBounded,
            (AbsoluteStartBound::Finite(_), AbsoluteEndBound::Finite(_)) => Openness::Bounded,
        }
    }
}

impl HasRelativity for AbsoluteBounds {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl PartialOrd for AbsoluteBounds {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteBounds {
    fn cmp(&self, other: &Self) -> Ordering {
        // using the comparison of self.end and other.end as a way to disambiguate when the two starts are equal
        // leads to side-effects, like when we store absolute bounds inside a BTreeSet, then if we use `range()`,
        // one can be considered out of the range when it shouldn't.
        self.start.cmp(&other.start)
    }
}

impl Display for AbsoluteBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = Ok(());

        result = result.and(write!(f, "Absolute bounds: "));

        match self.start() {
            AbsoluteStartBound::Finite(AbsoluteFiniteBound { time, inclusivity }) => {
                result = result.and(write!(f, "{time} ({inclusivity})"));
            },
            AbsoluteStartBound::InfinitePast => {
                result = result.and(write!(f, "Infinite past"));
            },
        }

        result = result.and(write!(f, " to "));

        match self.end() {
            AbsoluteEndBound::Finite(AbsoluteFiniteBound { time, inclusivity }) => {
                result = result.and(write!(f, "{time} ({inclusivity})"));
            },
            AbsoluteEndBound::InfiniteFuture => {
                result = result.and(write!(f, "Infinite future"));
            },
        }

        result
    }
}

impl<R> From<R> for AbsoluteBounds
where
    R: RangeBounds<Timestamp>,
{
    fn from(range: R) -> Self {
        AbsoluteBounds::new(
            AbsoluteStartBound::from(range.start_bound().cloned()),
            AbsoluteEndBound::from(range.end_bound().cloned()),
        )
    }
}

/// Errors that can occur when trying to convert [`EmptiableAbsoluteBounds`] into [`AbsoluteBounds`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AbsoluteBoundsFromEmptiableAbsoluteBoundsError {
    EmptyVariant,
}

impl Display for AbsoluteBoundsFromEmptiableAbsoluteBoundsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyVariant => write!(f, "Provided EmptiableAbsoluteBounds was empty"),
        }
    }
}

impl Error for AbsoluteBoundsFromEmptiableAbsoluteBoundsError {}

impl TryFrom<EmptiableAbsoluteBounds> for AbsoluteBounds {
    type Error = AbsoluteBoundsFromEmptiableAbsoluteBoundsError;

    fn try_from(value: EmptiableAbsoluteBounds) -> Result<Self, Self::Error> {
        match value {
            EmptiableAbsoluteBounds::Empty => Err(AbsoluteBoundsFromEmptiableAbsoluteBoundsError::EmptyVariant),
            EmptiableAbsoluteBounds::Bound(bounds) => Ok(bounds),
        }
    }
}


/// An absolute end bound
///
/// Represents the end bound of an interval, may it be infinitely in the future or at a precise point in time,
/// in which case it contains an [`AbsoluteFiniteBound`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum AbsoluteEndBound {
    Finite(AbsoluteFiniteBound),
    InfiniteFuture,
}

impl AbsoluteEndBound {
    /// Returns whether it is of the [`Finite`](AbsoluteEndBound::Finite) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound};
    /// let infinite_end_bound = AbsoluteEndBound::InfiniteFuture;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_end_bound = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(time));
    ///
    /// assert!(finite_end_bound.is_finite());
    /// assert!(!infinite_end_bound.is_finite());
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    /// Returns whether it is of the [`InfiniteFuture`](AbsoluteEndBound::InfiniteFuture) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound};
    /// let infinite_end_bound = AbsoluteEndBound::InfiniteFuture;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_end_bound = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(time));
    ///
    /// assert!(infinite_end_bound.is_infinite_future());
    /// assert!(!finite_end_bound.is_infinite_future());
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn is_infinite_future(&self) -> bool {
        matches!(self, Self::InfiniteFuture)
    }

    /// Returns the content of the [`Finite`](AbsoluteEndBound::Finite) variant
    ///
    /// Consumes `self` and puts the content of the [`Finite`](AbsoluteEndBound::Finite) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound};
    /// let infinite_end_bound = AbsoluteEndBound::InfiniteFuture;
    ///
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    /// let finite_end_bound = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(time));
    ///
    /// assert_eq!(finite_end_bound.finite(), Some(AbsoluteFiniteBound::new(time)));
    /// assert_eq!(infinite_end_bound.finite(), None);
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn finite(self) -> Option<AbsoluteFiniteBound> {
        match self {
            Self::Finite(finite) => Some(finite),
            Self::InfiniteFuture => None,
        }
    }

    /// Returns the opposite [`AbsoluteStartBound`]
    ///
    /// If the [`AbsoluteEndBound`] is of the [`InfiniteFuture`](AbsoluteEndBound::InfiniteFuture) variant,
    /// then the method returns [`None`].
    /// Otherwise, if the [`AbsoluteEndBound`] is finite, then an [`AbsoluteStartBound`] is created
    /// with the same time, but the opposite [`BoundInclusivity`].
    ///
    /// This is used for example for determining the first point in time after this bound ends.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound};
    /// let time = "2025-01-01 08:00:00Z".parse::<Timestamp>()?;
    ///
    /// let end_first_shift = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(time));
    /// let break_start = end_first_shift
    ///     .opposite()
    ///     .expect("provided a finite bound");
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<AbsoluteStartBound> {
        match self {
            Self::Finite(finite) => Some(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                finite.time(),
                finite.inclusivity().opposite(),
            ))),
            Self::InfiniteFuture => None,
        }
    }
}

impl PartialOrd for AbsoluteEndBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AbsoluteEndBound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (AbsoluteEndBound::InfiniteFuture, AbsoluteEndBound::InfiniteFuture) => Ordering::Equal,
            (AbsoluteEndBound::InfiniteFuture, AbsoluteEndBound::Finite(_)) => Ordering::Greater,
            (AbsoluteEndBound::Finite(_), AbsoluteEndBound::InfiniteFuture) => Ordering::Less,
            (
                AbsoluteEndBound::Finite(AbsoluteFiniteBound {
                    time: time_og,
                    inclusivity: inclusivity_og,
                }),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound {
                    time: time_other,
                    inclusivity: inclusivity_other,
                }),
            ) => {
                let time_cmp = time_og.cmp(time_other);

                if matches!(time_cmp, Ordering::Less | Ordering::Greater) {
                    return time_cmp;
                }

                match (inclusivity_og, inclusivity_other) {
                    (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
                    | (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => Ordering::Equal,
                    (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive) => Ordering::Greater,
                    (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => Ordering::Less,
                }
            },
        }
    }
}

impl PartialEq<AbsoluteStartBound> for AbsoluteEndBound {
    fn eq(&self, other: &AbsoluteStartBound) -> bool {
        other.eq(self)
    }
}

impl PartialOrd<AbsoluteStartBound> for AbsoluteEndBound {
    fn partial_cmp(&self, other: &AbsoluteStartBound) -> Option<Ordering> {
        match (self, other) {
            (AbsoluteEndBound::InfiniteFuture, _) | (_, AbsoluteStartBound::InfinitePast) => Some(Ordering::Greater),
            (
                AbsoluteEndBound::Finite(AbsoluteFiniteBound {
                    time: end_time,
                    inclusivity: end_inclusivity,
                }),
                AbsoluteStartBound::Finite(AbsoluteFiniteBound {
                    time: start_time,
                    inclusivity: start_inclusivity,
                }),
            ) => match end_time.cmp(start_time) {
                Ordering::Less => Some(Ordering::Less),
                Ordering::Equal => {
                    let disambiguated_bound_overlap =
                        BoundOverlapAmbiguity::EndStart(*end_inclusivity, *start_inclusivity)
                            .disambiguate_using_rule_set(BoundOverlapDisambiguationRuleSet::Strict);

                    match disambiguated_bound_overlap {
                        DisambiguatedBoundOverlap::Before => Some(Ordering::Greater),
                        DisambiguatedBoundOverlap::Equal => Some(Ordering::Equal),
                        DisambiguatedBoundOverlap::After => Some(Ordering::Less),
                    }
                },
                Ordering::Greater => Some(Ordering::Greater),
            },
        }
    }
}

impl Display for AbsoluteEndBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = Ok(());
        result = result.and(write!(f, "Absolute end: "));

        match self {
            Self::Finite(AbsoluteFiniteBound { time, inclusivity }) => {
                result = result.and(write!(f, "{time} ({inclusivity})"));
            },
            Self::InfiniteFuture => {
                result = result.and(write!(f, "Infinite future"));
            },
        }

        result
    }
}

impl From<AbsoluteFiniteBound> for AbsoluteEndBound {
    fn from(value: AbsoluteFiniteBound) -> Self {
        Self::Finite(value)
    }
}

impl From<Bound<Timestamp>> for AbsoluteEndBound {
    fn from(bound: Bound<Timestamp>) -> Self {
        match bound {
            Bound::Included(time) => AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                time,
                BoundInclusivity::Inclusive,
            )),
            Bound::Excluded(time) => AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                time,
                BoundInclusivity::Exclusive,
            )),
            Bound::Unbounded => AbsoluteEndBound::InfiniteFuture,
        }
    }
}

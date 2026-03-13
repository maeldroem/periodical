
/// A relative start bound
///
/// Represents the start bound of an interval, may it be infinitely in the past or at a precise offset,
/// in which case it contains an [`RelativeFiniteBound`].
///
/// Contrary to specific relative interval types, both [`RelativeStartBound`] and [`RelativeEndBound`] use an offset,
/// and not an offset for the start and a length for the end.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum RelativeStartBound {
    Finite(RelativeFiniteBound),
    InfinitePast,
}

impl RelativeStartBound {
    /// Returns whether it is of the [`Finite`](RelativeStartBound::Finite) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBound, RelativeStartBound};
    /// let infinite_start_bound = RelativeStartBound::InfinitePast;
    /// let finite_start_bound = RelativeStartBound::Finite(
    ///     RelativeFiniteBound::new(SignedDuration::hours(1))
    /// );
    ///
    /// assert!(finite_start_bound.is_finite());
    /// assert!(!infinite_start_bound.is_finite());
    /// ```
    #[must_use]
    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    /// Returns whether it is of the [`InfinitePast`](RelativeStartBound::InfinitePast) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBound, RelativeStartBound};
    /// let infinite_start_bound = RelativeStartBound::InfinitePast;
    /// let finite_start_bound = RelativeStartBound::Finite(
    ///     RelativeFiniteBound::new(SignedDuration::hours(1))
    /// );
    ///
    /// assert!(infinite_start_bound.is_infinite_past());
    /// assert!(!finite_start_bound.is_infinite_past());
    /// ```
    #[must_use]
    pub fn is_infinite_past(&self) -> bool {
        matches!(self, Self::InfinitePast)
    }

    /// Returns the content of the [`Finite`](RelativeStartBound::Finite) variant
    ///
    /// Consumes `self` and puts the content of the [`Finite`](RelativeStartBound::Finite) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBound, RelativeStartBound};
    /// let infinite_start_bound = RelativeStartBound::InfinitePast;
    /// let finite_start_bound = RelativeStartBound::Finite(
    ///     RelativeFiniteBound::new(SignedDuration::hours(1))
    /// );
    ///
    /// assert_eq!(finite_start_bound.finite(), Some(RelativeFiniteBound::new(SignedDuration::hours(1))));
    /// assert_eq!(infinite_start_bound.finite(), None);
    /// ```
    #[must_use]
    pub fn finite(self) -> Option<RelativeFiniteBound> {
        match self {
            Self::Finite(finite) => Some(finite),
            Self::InfinitePast => None,
        }
    }

    /// Returns the opposite [`RelativeEndBound`]
    ///
    /// If the [`RelativeStartBound`] is of the [`InfinitePast`](RelativeStartBound::InfinitePast) variant,
    /// then the method returns [`None`].
    /// Otherwise, if the [`RelativeStartBound`] is finite, then an [`RelativeEndBound`] is created
    /// with the same time, but the opposite [`BoundInclusivity`].
    ///
    /// This is used for example for determining the last point in time before this bound begins.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::SignedDuration;
    /// # use periodical::intervals::relative::{RelativeFiniteBound, RelativeStartBound};
    /// let start_second_part_my_shift = RelativeStartBound::Finite(
    ///     RelativeFiniteBound::new(SignedDuration::hours(3))
    /// );
    /// let break_end_before_shift = start_second_part_my_shift
    ///     .opposite()
    ///     .expect("provided a finite bound");
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Option<RelativeEndBound> {
        match self {
            Self::Finite(finite) => Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                finite.offset(),
                finite.inclusivity().opposite(),
            ))),
            Self::InfinitePast => None,
        }
    }
}

impl PartialEq<RelativeEndBound> for RelativeStartBound {
    fn eq(&self, other: &RelativeEndBound) -> bool {
        let RelativeStartBound::Finite(RelativeFiniteBound {
            offset: start_offset,
            inclusivity: start_inclusivity,
        }) = self
        else {
            return false;
        };
        let RelativeEndBound::Finite(RelativeFiniteBound {
            offset: end_offset,
            inclusivity: end_inclusivity,
        }) = other
        else {
            return false;
        };

        // If the offsets are equal, anything other than double inclusive bounds is invalid
        start_offset == end_offset
            && *start_inclusivity == BoundInclusivity::Inclusive
            && *end_inclusivity == BoundInclusivity::Inclusive
    }
}

impl PartialOrd for RelativeStartBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RelativeStartBound {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (RelativeStartBound::InfinitePast, RelativeStartBound::InfinitePast) => Ordering::Equal,
            (RelativeStartBound::InfinitePast, RelativeStartBound::Finite(_)) => Ordering::Less,
            (RelativeStartBound::Finite(_), RelativeStartBound::InfinitePast) => Ordering::Greater,
            (
                RelativeStartBound::Finite(RelativeFiniteBound {
                    offset: offset_og,
                    inclusivity: inclusivity_og,
                }),
                RelativeStartBound::Finite(RelativeFiniteBound {
                    offset: offset_other,
                    inclusivity: inclusivity_other,
                }),
            ) => {
                let offset_cmp = offset_og.cmp(offset_other);

                if matches!(offset_cmp, Ordering::Less | Ordering::Greater) {
                    return offset_cmp;
                }

                match (inclusivity_og, inclusivity_other) {
                    (BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
                    | (BoundInclusivity::Exclusive, BoundInclusivity::Exclusive) => Ordering::Equal,
                    (BoundInclusivity::Inclusive, BoundInclusivity::Exclusive) => Ordering::Less,
                    (BoundInclusivity::Exclusive, BoundInclusivity::Inclusive) => Ordering::Greater,
                }
            },
        }
    }
}

impl PartialOrd<RelativeEndBound> for RelativeStartBound {
    fn partial_cmp(&self, other: &RelativeEndBound) -> Option<Ordering> {
        match (self, other) {
            (RelativeStartBound::InfinitePast, _) | (_, RelativeEndBound::InfiniteFuture) => Some(Ordering::Less),
            (
                RelativeStartBound::Finite(RelativeFiniteBound {
                    offset: start_offset,
                    inclusivity: start_inclusivity,
                }),
                RelativeEndBound::Finite(RelativeFiniteBound {
                    offset: end_offset,
                    inclusivity: end_inclusivity,
                }),
            ) => match start_offset.cmp(end_offset) {
                Ordering::Less => Some(Ordering::Less),
                Ordering::Equal => {
                    let disambiguated_bound_overlap =
                        BoundOverlapAmbiguity::StartEnd(*start_inclusivity, *end_inclusivity)
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

impl Display for RelativeStartBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = Ok(());
        result = result.and(write!(f, "Relative start: "));

        match self {
            Self::Finite(RelativeFiniteBound { offset, inclusivity }) => {
                result = result.and(write!(f, "{offset} ({inclusivity})"));
            },
            Self::InfinitePast => {
                result = result.and(write!(f, "Infinite past"));
            },
        }

        result
    }
}

impl From<RelativeFiniteBound> for RelativeStartBound {
    fn from(value: RelativeFiniteBound) -> Self {
        Self::Finite(value)
    }
}

impl From<Bound<SignedDuration>> for RelativeStartBound {
    fn from(bound: Bound<SignedDuration>) -> Self {
        match bound {
            Bound::Included(offset) => RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                offset,
                BoundInclusivity::Inclusive,
            )),
            Bound::Excluded(offset) => RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                offset,
                BoundInclusivity::Exclusive,
            )),
            Bound::Unbounded => RelativeStartBound::InfinitePast,
        }
    }
}

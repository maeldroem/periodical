
/// Possession of possibly empty relative bounds
pub trait HasEmptiableRelativeBounds {
    /// Returns the [`EmptiableRelativeBounds`] of the object
    #[must_use]
    fn emptiable_rel_bounds(&self) -> EmptiableRelativeBounds;

    /// Returns an [`Option`] of [the relative start bound](RelativeStartBound) of the object
    #[must_use]
    fn partial_rel_start(&self) -> Option<RelativeStartBound>;

    /// Returns an [`Option`] of [the relative end bound](RelativeEndBound) of the object
    #[must_use]
    fn partial_rel_end(&self) -> Option<RelativeEndBound>;
}

/// All implementors of [`HasRelativeBounds`] implement [`HasEmptiableRelativeBounds`].
/// This could change in the future to separate emptiable from non-emptiable bounds.
impl<T> HasEmptiableRelativeBounds for T
where
    T: HasRelativeBounds,
{
    fn emptiable_rel_bounds(&self) -> EmptiableRelativeBounds {
        EmptiableRelativeBounds::Bound(self.rel_bounds())
    }

    fn partial_rel_start(&self) -> Option<RelativeStartBound> {
        Some(self.rel_start())
    }

    fn partial_rel_end(&self) -> Option<RelativeEndBound> {
        Some(self.rel_end())
    }
}

/// Enum containing [`RelativeBounds`] but with support for [empty intervals](EmptyInterval)
///
/// For more information, check [`RelativeBounds`], [`EmptyInterval`],
/// or [`crate::intervals` module documentation](crate::intervals).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum EmptiableRelativeBounds {
    Empty,
    Bound(RelativeBounds),
}

impl EmptiableRelativeBounds {
    /// Returns the content of the [`Bound`](EmptiableRelativeBounds::Bound) variant
    ///
    /// Consumes `self` and puts the content of the [`Bound`](EmptiableRelativeBounds::Bound) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::{
    /// #     EmptiableRelativeBounds, RelativeBounds, RelativeEndBound, RelativeStartBound,
    /// # };
    /// let bounds = RelativeBounds::new(
    ///     RelativeStartBound::InfinitePast,
    ///     RelativeEndBound::InfiniteFuture,
    /// );
    /// // Cloning is only for making the use of `bounds` okay in the following assertions
    /// let bound_emptiable_bounds = EmptiableRelativeBounds::Bound(bounds.clone());
    /// let empty_emptiable_bounds = EmptiableRelativeBounds::Empty;
    ///
    /// assert_eq!(bound_emptiable_bounds.bound(), Some(bounds));
    /// assert_eq!(empty_emptiable_bounds.bound(), None);
    /// ```
    #[must_use]
    pub fn bound(self) -> Option<RelativeBounds> {
        match self {
            EmptiableRelativeBounds::Empty => None,
            EmptiableRelativeBounds::Bound(bound) => Some(bound),
        }
    }

    /// Compares two [`EmptiableRelativeBounds`], but if they have the same start, order by decreasing length
    ///
    /// Uses [`RelativeBounds::ord_by_start_and_inv_length`] under the hood for
    /// the [`Bound`](EmptiableRelativeBounds::Bound) variants and [`EmptiableRelativeBounds::cmp`]
    /// for the [`Empty`](EmptiableRelativeBounds::Empty) variants (which will just place all empty bounds before
    /// any bound bounds).
    ///
    /// Don't rely on this method for checking for equality of start, as it will produce other [`Ordering`]s if their
    /// lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::relative::EmptiableRelativeBounds;
    /// # let mut bounds: [EmptiableRelativeBounds; 0] = [];
    /// bounds.sort_by(EmptiableRelativeBounds::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        match (self, other) {
            (EmptiableRelativeBounds::Bound(og_rel_bounds), EmptiableRelativeBounds::Bound(other_rel_bounds)) => {
                og_rel_bounds.ord_by_start_and_inv_length(other_rel_bounds)
            },
            _ => self.cmp(other),
        }
    }
}

impl Interval for EmptiableRelativeBounds {}

impl HasEmptiableRelativeBounds for EmptiableRelativeBounds {
    fn emptiable_rel_bounds(&self) -> EmptiableRelativeBounds {
        self.clone()
    }

    fn partial_rel_start(&self) -> Option<RelativeStartBound> {
        match self {
            Self::Empty => None,
            Self::Bound(bounds) => Some(*bounds.start()),
        }
    }

    fn partial_rel_end(&self) -> Option<RelativeEndBound> {
        match self {
            Self::Empty => None,
            Self::Bound(bounds) => Some(*bounds.end()),
        }
    }
}

impl Emptiable for EmptiableRelativeBounds {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }
}

impl HasDuration for EmptiableRelativeBounds {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bound(bound) => bound.duration(),
            Self::Empty => IntervalDuration::Finite(SignedDuration::zero(), Epsilon::None),
        }
    }
}

impl HasOpenness for EmptiableRelativeBounds {
    fn openness(&self) -> Openness {
        match self {
            Self::Bound(bound) => bound.openness(),
            Self::Empty => Openness::Empty,
        }
    }
}

impl HasRelativity for EmptiableRelativeBounds {
    fn relativity(&self) -> Relativity {
        Relativity::Relative
    }
}

impl PartialOrd for EmptiableRelativeBounds {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EmptiableRelativeBounds {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (EmptiableRelativeBounds::Empty, EmptiableRelativeBounds::Empty) => Ordering::Equal,
            (EmptiableRelativeBounds::Empty, EmptiableRelativeBounds::Bound(_)) => Ordering::Less,
            (EmptiableRelativeBounds::Bound(_), EmptiableRelativeBounds::Empty) => Ordering::Greater,
            (EmptiableRelativeBounds::Bound(og_rel_bounds), EmptiableRelativeBounds::Bound(other_rel_bounds)) => {
                og_rel_bounds.cmp(other_rel_bounds)
            },
        }
    }
}

impl Display for EmptiableRelativeBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "Empty relative interval bounds"),
            Self::Bound(bounds) => write!(f, "{bounds}"),
        }
    }
}

impl From<RelativeBounds> for EmptiableRelativeBounds {
    fn from(value: RelativeBounds) -> Self {
        EmptiableRelativeBounds::Bound(value)
    }
}

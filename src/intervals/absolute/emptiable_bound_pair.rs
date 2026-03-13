
/// Possession of possibly empty absolute bounds
pub trait HasEmptiableAbsoluteBounds {
    /// Returns the [`EmptiableAbsoluteBounds`] of the object
    #[must_use]
    fn emptiable_abs_bounds(&self) -> EmptiableAbsoluteBounds;

    /// Returns an [`Option`] of [the absolute start bound](AbsoluteStartBound) of the object
    #[must_use]
    fn partial_abs_start(&self) -> Option<AbsoluteStartBound>;

    /// Returns an [`Option`] of [the absolute end bound](AbsoluteEndBound) of the object
    #[must_use]
    fn partial_abs_end(&self) -> Option<AbsoluteEndBound>;
}

/// All implementors of [`HasAbsoluteBounds`] implement [`HasEmptiableAbsoluteBounds`].
/// This could change in the future to separate emptiable from non-emptiable bounds.
impl<T> HasEmptiableAbsoluteBounds for T
where
    T: HasAbsoluteBounds,
{
    fn emptiable_abs_bounds(&self) -> EmptiableAbsoluteBounds {
        EmptiableAbsoluteBounds::Bound(self.abs_bounds())
    }

    fn partial_abs_start(&self) -> Option<AbsoluteStartBound> {
        Some(self.abs_start())
    }

    fn partial_abs_end(&self) -> Option<AbsoluteEndBound> {
        Some(self.abs_end())
    }
}

/// Enum containing [`AbsoluteBounds`] but with support for [empty intervals](EmptyInterval)
///
/// For more information, check [`AbsoluteBounds`], [`EmptyInterval`],
/// or [`crate::intervals` module documentation](crate::intervals).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum EmptiableAbsoluteBounds {
    Empty,
    Bound(AbsoluteBounds),
}

impl EmptiableAbsoluteBounds {
    /// Returns the content of the [`Bound`](EmptiableAbsoluteBounds::Bound) variant
    ///
    /// Consumes `self` and puts the content of the [`Bound`](EmptiableAbsoluteBounds::Bound) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
    /// # };
    /// let bounds = AbsoluteBounds::new(
    ///     AbsoluteStartBound::InfinitePast,
    ///     AbsoluteEndBound::InfiniteFuture,
    /// );
    /// // Cloning is only for making the use of `bounds` okay in the following assertions
    /// let bound_emptiable_bounds = EmptiableAbsoluteBounds::Bound(bounds.clone());
    /// let empty_emptiable_bounds = EmptiableAbsoluteBounds::Empty;
    ///
    /// assert_eq!(bound_emptiable_bounds.bound(), Some(bounds));
    /// assert_eq!(empty_emptiable_bounds.bound(), None);
    /// ```
    #[must_use]
    pub fn bound(self) -> Option<AbsoluteBounds> {
        match self {
            EmptiableAbsoluteBounds::Empty => None,
            EmptiableAbsoluteBounds::Bound(bound) => Some(bound),
        }
    }

    /// Compares two [`EmptiableAbsoluteBounds`], but if they have the same start, order by decreasing length
    ///
    /// Uses [`AbsoluteBounds::ord_by_start_and_inv_length`] under the hood for
    /// the [`Bound`](EmptiableAbsoluteBounds::Bound) variants and [`EmptiableAbsoluteBounds::cmp`]
    /// for the [`Empty`](EmptiableAbsoluteBounds::Empty) variants (which will just place all empty bounds before
    /// any bound bounds).
    ///
    /// Don't rely on this method for checking for equality of start, as it will produce other [`Ordering`]s if their
    /// lengths don't match too.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::absolute::EmptiableAbsoluteBounds;
    /// # let mut bounds: [EmptiableAbsoluteBounds; 0] = [];
    /// bounds.sort_by(EmptiableAbsoluteBounds::ord_by_start_and_inv_length);
    /// ```
    #[must_use]
    pub fn ord_by_start_and_inv_length(&self, other: &Self) -> Ordering {
        match (self, other) {
            (EmptiableAbsoluteBounds::Bound(og_abs_bounds), EmptiableAbsoluteBounds::Bound(other_abs_bounds)) => {
                og_abs_bounds.ord_by_start_and_inv_length(other_abs_bounds)
            },
            _ => self.cmp(other),
        }
    }
}

impl Interval for EmptiableAbsoluteBounds {}

impl HasEmptiableAbsoluteBounds for EmptiableAbsoluteBounds {
    fn emptiable_abs_bounds(&self) -> EmptiableAbsoluteBounds {
        self.clone()
    }

    fn partial_abs_start(&self) -> Option<AbsoluteStartBound> {
        match self {
            Self::Empty => None,
            Self::Bound(bounds) => Some(*bounds.start()),
        }
    }

    fn partial_abs_end(&self) -> Option<AbsoluteEndBound> {
        match self {
            Self::Empty => None,
            Self::Bound(bounds) => Some(*bounds.end()),
        }
    }
}

impl Emptiable for EmptiableAbsoluteBounds {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }
}

impl HasDuration for EmptiableAbsoluteBounds {
    fn duration(&self) -> IntervalDuration {
        match self {
            Self::Bound(bound) => bound.duration(),
            Self::Empty => IntervalDuration::Finite(Duration::ZERO, Epsilon::None),
        }
    }
}

impl HasOpenness for EmptiableAbsoluteBounds {
    fn openness(&self) -> Openness {
        match self {
            Self::Bound(bound) => bound.openness(),
            Self::Empty => Openness::Empty,
        }
    }
}

impl HasRelativity for EmptiableAbsoluteBounds {
    fn relativity(&self) -> Relativity {
        Relativity::Absolute
    }
}

impl PartialOrd for EmptiableAbsoluteBounds {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for EmptiableAbsoluteBounds {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (EmptiableAbsoluteBounds::Empty, EmptiableAbsoluteBounds::Empty) => Ordering::Equal,
            (EmptiableAbsoluteBounds::Empty, EmptiableAbsoluteBounds::Bound(_)) => Ordering::Less,
            (EmptiableAbsoluteBounds::Bound(_), EmptiableAbsoluteBounds::Empty) => Ordering::Greater,
            (EmptiableAbsoluteBounds::Bound(og_abs_bounds), EmptiableAbsoluteBounds::Bound(other_abs_bounds)) => {
                og_abs_bounds.cmp(other_abs_bounds)
            },
        }
    }
}

impl Display for EmptiableAbsoluteBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "Empty absolute interval bounds"),
            Self::Bound(bounds) => write!(f, "{bounds}"),
        }
    }
}

impl From<AbsoluteBounds> for EmptiableAbsoluteBounds {
    fn from(value: AbsoluteBounds) -> Self {
        EmptiableAbsoluteBounds::Bound(value)
    }
}


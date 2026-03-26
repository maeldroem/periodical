//! Relativity conversion
//!
//! Conversion from absolute to relative is defined by [`ToRelative`].
//! Its opposite, conversion from relative to absolute, is defined by [`ToAbsolute`].

use jiff::Timestamp;

use crate::intervals::absolute::{
    AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound, BoundedAbsoluteInterval, EmptiableAbsoluteBoundPair, EmptiableAbsoluteInterval, HalfBoundedAbsoluteInterval, HasAbsoluteBoundPair
};
use crate::intervals::meta::HasBoundInclusivity;
use crate::intervals::relative::{
    BoundedRelativeInterval, EmptiableRelativeBoundPair, EmptiableRelativeInterval, HalfBoundedRelativeInterval, HasRelativeBoundPair, RelativeBoundPair, RelativeEndBound, RelativeFiniteBound, RelativeInterval, RelativeStartBound
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

macro_rules! to_absolute_impl_reflective {
    ([$($implementor:ty),* $(,)?]) => {
        $(
            impl ToAbsolute for $implementor {
                type AbsoluteType = Self;

                fn to_absolute<D>(&self, _reference_time: D) -> Self::AbsoluteType
                where
                    D: Into<Timestamp>,
                {
                    self.clone()
                }
            }
        )*
    };
}

macro_rules! to_relative_impl_reflective {
    ([$($implementor:ty),* $(,)?]) => {
        $(
            impl ToRelative for $implementor {
                type RelativeType = Self;

                fn to_relative<D>(&self, _reference_time: D) -> Self::RelativeType
                where
                    D: Into<Timestamp>,
                {
                    self.clone()
                }
            }
        )*
    };
}

/// Conversion into absolute
///
/// This trait is reflexive: absolute structures should implement [`ToAbsolute`].
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::{SignedDuration, Zoned};
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
/// # use periodical::intervals::ops::relativity_conversion::ToAbsolute;
/// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBound};
/// let rel_interval = RelativeBoundPair::new(
///     RelativeFiniteBound::new(
///         SignedDuration::from_hours(8),
///     ).to_start_bound(),
///     RelativeFiniteBound::new(
///         SignedDuration::from_hours(16),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     rel_interval.to_absolute("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
///     AbsoluteBoundPair::new(
///         AbsoluteFiniteBound::new(
///             "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///         ).to_start_bound(),
///         AbsoluteFiniteBound::new(
///             "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///         ).to_end_bound(),
///     ),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait ToAbsolute {
    type AbsoluteType;

    /// Converts into absolute
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::{SignedDuration, Zoned};
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::ops::relativity_conversion::ToAbsolute;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBound};
    /// let rel_interval = RelativeBoundPair::new(
    ///     RelativeFiniteBound::new(
    ///         SignedDuration::from_hours(8),
    ///     ).to_start_bound(),
    ///     RelativeFiniteBound::new(
    ///         SignedDuration::from_hours(16),
    ///     ).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     rel_interval.to_absolute("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         ).to_start_bound(),
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///         ).to_end_bound(),
    ///     ),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn to_absolute<D>(&self, reference_time: D) -> Self::AbsoluteType
    where
        D: Into<Timestamp>;
}

to_absolute_impl_reflective!([
    UnboundedInterval,
    EmptyInterval,
    AbsoluteFiniteBound,
    AbsoluteStartBound,
    AbsoluteEndBound,
    AbsoluteBoundPair,
    EmptiableAbsoluteBoundPair,
    BoundedAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    AbsoluteInterval,
    EmptiableAbsoluteInterval,
]);

impl ToAbsolute for RelativeFiniteBound {
    type AbsoluteType = AbsoluteFiniteBound;

    fn to_absolute<D>(&self, reference_time: D) -> Self::AbsoluteType
    where
        D: Into<Timestamp>,
    {
        AbsoluteFiniteBound::new_with_inclusivity(reference_time.into() + self.offset(), self.inclusivity())
    }
}

impl ToAbsolute for RelativeStartBound {
    type AbsoluteType = AbsoluteStartBound;

    fn to_absolute<D>(&self, reference_time: D) -> Self::AbsoluteType
    where
        D: Into<Timestamp>,
    {
        match self {
            RelativeStartBound::InfinitePast => AbsoluteStartBound::InfinitePast,
            RelativeStartBound::Finite(relative_finite) => {
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    reference_time.into() + relative_finite.offset(),
                    relative_finite.inclusivity(),
                ))
            },
        }
    }
}

impl ToAbsolute for RelativeEndBound {
    type AbsoluteType = AbsoluteEndBound;

    fn to_absolute<D>(&self, reference_time: D) -> Self::AbsoluteType
    where
        D: Into<Timestamp>,
    {
        match self {
            RelativeEndBound::InfiniteFuture => AbsoluteEndBound::InfiniteFuture,
            RelativeEndBound::Finite(relative_finite) => {
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    reference_time.into() + relative_finite.offset(),
                    relative_finite.inclusivity(),
                ))
            },
        }
    }
}

impl ToAbsolute for RelativeBoundPair {
    type AbsoluteType = AbsoluteBoundPair;

    fn to_absolute<D>(&self, reference_time: D) -> Self::AbsoluteType
    where
        D: Into<Timestamp>,
    {
        let reference_time = reference_time.into();

        AbsoluteBoundPair::new(
            self.rel_start().to_absolute(reference_time),
            self.rel_end().to_absolute(reference_time),
        )
    }
}

impl ToAbsolute for EmptiableRelativeBoundPair {
    type AbsoluteType = EmptiableAbsoluteBoundPair;

    fn to_absolute<D>(&self, reference_time: D) -> Self::AbsoluteType
    where
        D: Into<Timestamp>,
    {
        match self {
            Self::Empty => EmptiableAbsoluteBoundPair::Empty,
            Self::Bound(abs_bound_pair) => EmptiableAbsoluteBoundPair::Bound(abs_bound_pair.to_absolute(reference_time)),
        }
    }
}

impl ToAbsolute for BoundedRelativeInterval {
    type AbsoluteType = BoundedAbsoluteInterval;

    fn to_absolute<D>(&self, reference_time: D) -> Self::AbsoluteType
    where
        D: Into<Timestamp>,
    {
        let reference_time = reference_time.into();

        BoundedAbsoluteInterval::unchecked_new_with_inclusivity(
            reference_time + self.start(),
            self.start_inclusivity(),
            reference_time + self.end(),
            self.end_inclusivity(),
        )
    }
}

impl ToAbsolute for HalfBoundedRelativeInterval {
    type AbsoluteType = HalfBoundedAbsoluteInterval;

    fn to_absolute<D>(&self, reference_time: D) -> Self::AbsoluteType
    where
        D: Into<Timestamp>,
    {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            reference_time.into() + self.reference(),
            self.reference_inclusivity(),
            self.opening_direction(),
        )
    }
}

impl ToAbsolute for RelativeInterval {
    type AbsoluteType = AbsoluteInterval;

    fn to_absolute<D>(&self, reference_time: D) -> Self::AbsoluteType
    where
        D: Into<Timestamp>,
    {
        match self {
            Self::Bounded(bounded) => AbsoluteInterval::Bounded(bounded.to_absolute(reference_time)),
            Self::HalfBounded(half_bounded) => AbsoluteInterval::HalfBounded(half_bounded.to_absolute(reference_time)),
            Self::Unbounded(unbounded) => AbsoluteInterval::Unbounded(unbounded.to_absolute(reference_time)),
        }
    }
}

impl ToAbsolute for EmptiableRelativeInterval {
    type AbsoluteType = EmptiableAbsoluteInterval;

    fn to_absolute<D>(&self, reference_time: D) -> Self::AbsoluteType
    where
        D: Into<Timestamp>,
    {
        match self {
            Self::Bounded(bounded) => EmptiableAbsoluteInterval::Bounded(bounded.to_absolute(reference_time)),
            Self::HalfBounded(half_bounded) => EmptiableAbsoluteInterval::HalfBounded(half_bounded.to_absolute(reference_time)),
            Self::Unbounded(unbounded) => EmptiableAbsoluteInterval::Unbounded(unbounded.to_absolute(reference_time)),
            Self::Empty(empty) => EmptiableAbsoluteInterval::Empty(empty.to_absolute(reference_time)),
        }
    }
}

/// Conversion into relative
///
/// This trait is reflexive: relative structures should implement [`ToRelative`].
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::{SignedDuration, Zoned};
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
/// # use periodical::intervals::ops::relativity_conversion::ToRelative;
/// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBound};
/// let abs_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
///     ).to_end_bound(),
/// );
///
/// assert_eq!(
///     abs_interval.to_relative("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
///     RelativeBoundPair::new(
///         RelativeFiniteBound::new(
///             SignedDuration::from_hours(8),
///         ).to_start_bound(),
///         RelativeFiniteBound::new(
///             SignedDuration::from_hours(16),
///         ).to_end_bound(),
///     ),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait ToRelative {
    type RelativeType;

    /// Converts into relative
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::{SignedDuration, Zoned};
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::ops::relativity_conversion::ToRelative;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBound};
    /// let abs_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     ).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     abs_interval.to_relative("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()),
    ///     RelativeBoundPair::new(
    ///         RelativeFiniteBound::new(
    ///             SignedDuration::from_hours(8),
    ///         ).to_start_bound(),
    ///         RelativeFiniteBound::new(
    ///             SignedDuration::from_hours(16),
    ///         ).to_end_bound(),
    ///     ),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn to_relative<D>(&self, reference_time: D) -> Self::RelativeType
    where
        D: Into<Timestamp>;
}

to_relative_impl_reflective!([
    UnboundedInterval,
    EmptyInterval,
    RelativeFiniteBound,
    RelativeStartBound,
    RelativeEndBound,
    RelativeBoundPair,
    EmptiableRelativeBoundPair,
    BoundedRelativeInterval,
    HalfBoundedRelativeInterval,
    RelativeInterval,
    EmptiableRelativeInterval,
]);

impl ToRelative for AbsoluteFiniteBound {
    type RelativeType = RelativeFiniteBound;

    fn to_relative<D>(&self, reference_time: D) -> Self::RelativeType
    where
        D: Into<Timestamp>,
    {
        RelativeFiniteBound::new_with_inclusivity(self.time().duration_since(reference_time.into()), self.inclusivity())
    }
}

impl ToRelative for AbsoluteStartBound {
    type RelativeType = RelativeStartBound;

    fn to_relative<D>(&self, reference_time: D) -> Self::RelativeType
    where
        D: Into<Timestamp>,
    {
        match self {
            AbsoluteStartBound::InfinitePast => RelativeStartBound::InfinitePast,
            AbsoluteStartBound::Finite(absolute_finite) => {
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    absolute_finite.time().duration_since(reference_time.into()),
                    absolute_finite.inclusivity(),
                ))
            },
        }
    }
}

impl ToRelative for AbsoluteEndBound {
    type RelativeType = RelativeEndBound;

    fn to_relative<D>(&self, reference_time: D) -> Self::RelativeType
    where
        D: Into<Timestamp>,
    {
        match self {
            AbsoluteEndBound::InfiniteFuture => RelativeEndBound::InfiniteFuture,
            AbsoluteEndBound::Finite(absolute_finite) => {
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    absolute_finite.time().duration_since(reference_time.into()),
                    absolute_finite.inclusivity(),
                ))
            },
        }
    }
}

impl ToRelative for AbsoluteBoundPair {
    type RelativeType = RelativeBoundPair;

    fn to_relative<D>(&self, reference_time: D) -> Self::RelativeType
    where
        D: Into<Timestamp>,
    {
        let reference_time = reference_time.into();

        RelativeBoundPair::new(
            self.abs_start().to_relative(reference_time),
            self.abs_end().to_relative(reference_time),
        )
    }
}

impl ToRelative for EmptiableAbsoluteBoundPair {
    type RelativeType = EmptiableRelativeBoundPair;

    fn to_relative<D>(&self, reference_time: D) -> Self::RelativeType
    where
        D: Into<Timestamp>,
    {
        match self {
            Self::Empty => EmptiableRelativeBoundPair::Empty,
            Self::Bound(abs_bound_pair) => EmptiableRelativeBoundPair::Bound(abs_bound_pair.to_relative(reference_time)),
        }
    }
}

impl ToRelative for BoundedAbsoluteInterval {
    type RelativeType = BoundedRelativeInterval;

    fn to_relative<D>(&self, reference_time: D) -> Self::RelativeType
    where
        D: Into<Timestamp>,
    {
        let reference_time = reference_time.into();

        BoundedRelativeInterval::new_with_inclusivity(
            self.start().duration_since(reference_time),
            self.start_inclusivity(),
            self.end().duration_since(reference_time),
            self.end_inclusivity(),
        )
    }
}

impl ToRelative for HalfBoundedAbsoluteInterval {
    type RelativeType = HalfBoundedRelativeInterval;

    fn to_relative<D>(&self, reference_time: D) -> Self::RelativeType
    where
        D: Into<Timestamp>,
    {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            self.reference().duration_since(reference_time.into()),
            self.reference_inclusivity(),
            self.opening_direction(),
        )
    }
}

impl ToRelative for AbsoluteInterval {
    type RelativeType = RelativeInterval;

    fn to_relative<D>(&self, reference_time: D) -> Self::RelativeType
    where
        D: Into<Timestamp>,
    {
        match self {
            Self::Bounded(bounded) => RelativeInterval::Bounded(bounded.to_relative(reference_time)),
            Self::HalfBounded(half_bounded) => RelativeInterval::HalfBounded(half_bounded.to_relative(reference_time)),
            Self::Unbounded(unbounded) => RelativeInterval::Unbounded(unbounded.to_relative(reference_time)),
        }
    }
}

impl ToRelative for EmptiableAbsoluteInterval {
    type RelativeType = EmptiableRelativeInterval;

    fn to_relative<D>(&self, reference_time: D) -> Self::RelativeType
    where
        D: Into<Timestamp>,
    {
        match self {
            Self::Bounded(bounded) => EmptiableRelativeInterval::Bounded(bounded.to_relative(reference_time)),
            Self::HalfBounded(half_bounded) => EmptiableRelativeInterval::HalfBounded(half_bounded.to_relative(reference_time)),
            Self::Unbounded(unbounded) => EmptiableRelativeInterval::Unbounded(unbounded.to_relative(reference_time)),
            Self::Empty(empty) => EmptiableRelativeInterval::Empty(empty.to_relative(reference_time)),
        }
    }
}

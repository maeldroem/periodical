//! Relativity conversion
//!
//! Conversion from absolute to relative is defined by [`ToRelative`].
//! Its opposite, conversion from relative to absolute, is defined by
//! [`ToAbsolute`].

use jiff::Timestamp;

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
};
use crate::intervals::meta::HasBoundInclusivity;
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeInterval,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

macro_rules! to_absolute_impl_reflective {
    ([$($implementor:ty),* $(,)?]) => {
        $(
            impl ToAbsolute for $implementor {
                type AbsoluteType = Self;

                fn to_absolute(&self, _reference: Timestamp) -> Self::AbsoluteType {
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

                fn to_relative(&self, _reference: Timestamp) -> Self::RelativeType {
                    self.clone()
                }
            }
        )*
    };
}

/// Conversion into absolute
///
/// This trait is reflexive: absolute structures should implement
/// [`ToAbsolute`].
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
///     RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_start_bound(),
///     RelativeFiniteBound::new(SignedDuration::from_hours(16)).to_end_bound(),
/// );
///
/// assert_eq!(
///     rel_interval.to_absolute(
///         "2025-01-01 00:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp()
///     ),
///     AbsoluteBoundPair::new(
///         AbsoluteFiniteBound::new(
///             "2025-01-01 08:00:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///         )
///         .to_start_bound(),
///         AbsoluteFiniteBound::new(
///             "2025-01-01 16:00:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///         )
///         .to_end_bound(),
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
    ///     RelativeFiniteBound::new(SignedDuration::from_hours(8)).to_start_bound(),
    ///     RelativeFiniteBound::new(SignedDuration::from_hours(16)).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     rel_interval.to_absolute(
    ///         "2025-01-01 00:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp()
    ///     ),
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBound::new(
    ///             "2025-01-01 16:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_end_bound(),
    ///     ),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn to_absolute(&self, reference: Timestamp) -> Self::AbsoluteType;
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

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsoluteType {
        AbsoluteFiniteBound::new_with_inclusivity(reference + self.offset(), self.inclusivity())
    }
}

impl ToAbsolute for RelativeStartBound {
    type AbsoluteType = AbsoluteStartBound;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsoluteType {
        match self {
            RelativeStartBound::InfinitePast => AbsoluteStartBound::InfinitePast,
            RelativeStartBound::Finite(relative_finite) => AbsoluteFiniteBound::new_with_inclusivity(
                reference + relative_finite.offset(),
                relative_finite.inclusivity(),
            )
            .to_start_bound(),
        }
    }
}

impl ToAbsolute for RelativeEndBound {
    type AbsoluteType = AbsoluteEndBound;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsoluteType {
        match self {
            RelativeEndBound::InfiniteFuture => AbsoluteEndBound::InfiniteFuture,
            RelativeEndBound::Finite(relative_finite) => AbsoluteFiniteBound::new_with_inclusivity(
                reference + relative_finite.offset(),
                relative_finite.inclusivity(),
            )
            .to_end_bound(),
        }
    }
}

impl ToAbsolute for RelativeBoundPair {
    type AbsoluteType = AbsoluteBoundPair;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsoluteType {
        let reference = reference;

        AbsoluteBoundPair::new(
            self.rel_start().to_absolute(reference),
            self.rel_end().to_absolute(reference),
        )
    }
}

impl ToAbsolute for EmptiableRelativeBoundPair {
    type AbsoluteType = EmptiableAbsoluteBoundPair;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsoluteType {
        match self {
            Self::Empty => EmptiableAbsoluteBoundPair::Empty,
            Self::Bound(abs_bound_pair) => EmptiableAbsoluteBoundPair::Bound(abs_bound_pair.to_absolute(reference)),
        }
    }
}

impl ToAbsolute for BoundedRelativeInterval {
    type AbsoluteType = BoundedAbsoluteInterval;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsoluteType {
        BoundedAbsoluteInterval::unchecked_new_with_inclusivity(
            reference + self.start(),
            self.start_inclusivity(),
            reference + self.end(),
            self.end_inclusivity(),
        )
    }
}

impl ToAbsolute for HalfBoundedRelativeInterval {
    type AbsoluteType = HalfBoundedAbsoluteInterval;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsoluteType {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            reference + self.reference(),
            self.reference_inclusivity(),
            self.opening_direction(),
        )
    }
}

impl ToAbsolute for RelativeInterval {
    type AbsoluteType = AbsoluteInterval;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsoluteType {
        match self {
            Self::Bounded(bounded) => AbsoluteInterval::Bounded(bounded.to_absolute(reference)),
            Self::HalfBounded(half_bounded) => AbsoluteInterval::HalfBounded(half_bounded.to_absolute(reference)),
            Self::Unbounded(unbounded) => AbsoluteInterval::Unbounded(unbounded.to_absolute(reference)),
        }
    }
}

impl ToAbsolute for EmptiableRelativeInterval {
    type AbsoluteType = EmptiableAbsoluteInterval;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsoluteType {
        match self {
            Self::Bound(interval) => EmptiableAbsoluteInterval::Bound(interval.to_absolute(reference)),
            Self::Empty(empty) => EmptiableAbsoluteInterval::Empty(empty.to_absolute(reference)),
        }
    }
}

/// Conversion into relative
///
/// This trait is reflexive: relative structures should implement
/// [`ToRelative`].
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
///         "2025-01-01 08:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsoluteFiniteBound::new(
///         "2025-01-01 16:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_end_bound(),
/// );
///
/// assert_eq!(
///     abs_interval.to_relative(
///         "2025-01-01 00:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp()
///     ),
///     RelativeBoundPair::new(
///         RelativeFiniteBound::new(SignedDuration::from_hours(8),).to_start_bound(),
///         RelativeFiniteBound::new(SignedDuration::from_hours(16),).to_end_bound(),
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
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBound::new(
    ///         "2025-01-01 16:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     abs_interval.to_relative(
    ///         "2025-01-01 00:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp()
    ///     ),
    ///     RelativeBoundPair::new(
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(8),).to_start_bound(),
    ///         RelativeFiniteBound::new(SignedDuration::from_hours(16),).to_end_bound(),
    ///     ),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn to_relative(&self, reference: Timestamp) -> Self::RelativeType;
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

    fn to_relative(&self, reference: Timestamp) -> Self::RelativeType {
        RelativeFiniteBound::new_with_inclusivity(self.time().duration_since(reference), self.inclusivity())
    }
}

impl ToRelative for AbsoluteStartBound {
    type RelativeType = RelativeStartBound;

    fn to_relative(&self, reference: Timestamp) -> Self::RelativeType {
        match self {
            AbsoluteStartBound::InfinitePast => RelativeStartBound::InfinitePast,
            AbsoluteStartBound::Finite(absolute_finite) => RelativeFiniteBound::new_with_inclusivity(
                absolute_finite.time().duration_since(reference),
                absolute_finite.inclusivity(),
            )
            .to_start_bound(),
        }
    }
}

impl ToRelative for AbsoluteEndBound {
    type RelativeType = RelativeEndBound;

    fn to_relative(&self, reference: Timestamp) -> Self::RelativeType {
        match self {
            AbsoluteEndBound::InfiniteFuture => RelativeEndBound::InfiniteFuture,
            AbsoluteEndBound::Finite(absolute_finite) => RelativeFiniteBound::new_with_inclusivity(
                absolute_finite.time().duration_since(reference),
                absolute_finite.inclusivity(),
            )
            .to_end_bound(),
        }
    }
}

impl ToRelative for AbsoluteBoundPair {
    type RelativeType = RelativeBoundPair;

    fn to_relative(&self, reference: Timestamp) -> Self::RelativeType {
        let reference = reference;

        RelativeBoundPair::new(
            self.abs_start().to_relative(reference),
            self.abs_end().to_relative(reference),
        )
    }
}

impl ToRelative for EmptiableAbsoluteBoundPair {
    type RelativeType = EmptiableRelativeBoundPair;

    fn to_relative(&self, reference: Timestamp) -> Self::RelativeType {
        match self {
            Self::Empty => EmptiableRelativeBoundPair::Empty,
            Self::Bound(abs_bound_pair) => EmptiableRelativeBoundPair::Bound(abs_bound_pair.to_relative(reference)),
        }
    }
}

impl ToRelative for BoundedAbsoluteInterval {
    type RelativeType = BoundedRelativeInterval;

    fn to_relative(&self, reference: Timestamp) -> Self::RelativeType {
        let reference = reference;

        BoundedRelativeInterval::new_with_inclusivity(
            self.start().duration_since(reference),
            self.start_inclusivity(),
            self.end().duration_since(reference),
            self.end_inclusivity(),
        )
    }
}

impl ToRelative for HalfBoundedAbsoluteInterval {
    type RelativeType = HalfBoundedRelativeInterval;

    fn to_relative(&self, reference: Timestamp) -> Self::RelativeType {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            self.reference().duration_since(reference),
            self.reference_inclusivity(),
            self.opening_direction(),
        )
    }
}

impl ToRelative for AbsoluteInterval {
    type RelativeType = RelativeInterval;

    fn to_relative(&self, reference: Timestamp) -> Self::RelativeType {
        match self {
            Self::Bounded(bounded) => RelativeInterval::Bounded(bounded.to_relative(reference)),
            Self::HalfBounded(half_bounded) => RelativeInterval::HalfBounded(half_bounded.to_relative(reference)),
            Self::Unbounded(unbounded) => RelativeInterval::Unbounded(unbounded.to_relative(reference)),
        }
    }
}

impl ToRelative for EmptiableAbsoluteInterval {
    type RelativeType = EmptiableRelativeInterval;

    fn to_relative(&self, reference: Timestamp) -> Self::RelativeType {
        match self {
            Self::Bound(interval) => EmptiableRelativeInterval::Bound(interval.to_relative(reference)),
            Self::Empty(empty) => EmptiableRelativeInterval::Empty(empty.to_relative(reference)),
        }
    }
}

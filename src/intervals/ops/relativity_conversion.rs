//! Relativity conversion
//!
//! Conversion from absolute to relative is defined by [`ToRelative`].
//! Its opposite, conversion from relative to absolute, is defined by
//! [`ToAbsolute`].

use jiff::Timestamp;

use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
};
use crate::intervals::meta::{HasBoundInclusivity, HasOpeningDirection};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBoundPosition,
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
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
/// # use periodical::intervals::ops::relativity_conversion::ToAbsolute;
/// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition};
/// let rel_interval = RelativeBoundPair::new(
///     RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8)).to_start_bound(),
///     RelativeFiniteBoundPosition::new(SignedDuration::from_hours(16)).to_end_bound(),
/// );
///
/// assert_eq!(
///     rel_interval.to_absolute(
///         "2025-01-01 00:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp()
///     ),
///     AbsoluteBoundPair::new(
///         AbsoluteFiniteBoundPosition::new(
///             "2025-01-01 08:00:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///         )
///         .to_start_bound(),
///         AbsoluteFiniteBoundPosition::new(
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
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// # use periodical::intervals::ops::relativity_conversion::ToAbsolute;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition};
    /// let rel_interval = RelativeBoundPair::new(
    ///     RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8)).to_start_bound(),
    ///     RelativeFiniteBoundPosition::new(SignedDuration::from_hours(16)).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     rel_interval.to_absolute(
    ///         "2025-01-01 00:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp()
    ///     ),
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsoluteFiniteBoundPosition::new(
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
    AbsoluteFiniteBoundPosition,
    AbsoluteStartBound,
    AbsoluteEndBound,
    AbsoluteBoundPair,
    EmptiableAbsoluteBoundPair,
    BoundedAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    AbsoluteInterval,
    EmptiableAbsoluteInterval,
]);

impl ToAbsolute for RelativeFiniteBoundPosition {
    type AbsoluteType = AbsoluteFiniteBoundPosition;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsoluteType {
        AbsoluteFiniteBoundPosition::new_with_inclusivity(reference + self.offset(), self.inclusivity())
    }
}

impl ToAbsolute for RelativeStartBound {
    type AbsoluteType = AbsoluteStartBound;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsoluteType {
        match self {
            RelativeStartBound::InfinitePast => AbsoluteStartBound::InfinitePast,
            RelativeStartBound::Finite(relative_finite) => AbsoluteFiniteBoundPosition::new_with_inclusivity(
                reference + relative_finite.pos().offset(),
                relative_finite.pos().inclusivity(),
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
            RelativeEndBound::Finite(relative_finite) => AbsoluteFiniteBoundPosition::new_with_inclusivity(
                reference + relative_finite.pos().offset(),
                relative_finite.pos().inclusivity(),
            )
            .to_end_bound(),
        }
    }
}

impl ToAbsolute for RelativeBoundPair {
    type AbsoluteType = AbsoluteBoundPair;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsoluteType {
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
        BoundedAbsoluteInterval::unchecked_new_from_times_and_inclusivities(
            reference + self.start_offset(),
            self.start_inclusivity(),
            reference + self.end_offset(),
            self.end_inclusivity(),
        )
    }
}

impl ToAbsolute for HalfBoundedRelativeInterval {
    type AbsoluteType = HalfBoundedAbsoluteInterval;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsoluteType {
        HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
            reference + self.reference_offset(),
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
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
/// # use periodical::intervals::ops::relativity_conversion::ToRelative;
/// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition};
/// let abs_interval = AbsoluteBoundPair::new(
///     AbsoluteFiniteBoundPosition::new(
///         "2025-01-01 08:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsoluteFiniteBoundPosition::new(
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
///         RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8),).to_start_bound(),
///         RelativeFiniteBoundPosition::new(SignedDuration::from_hours(16),).to_end_bound(),
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
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBoundPosition};
    /// # use periodical::intervals::ops::relativity_conversion::ToRelative;
    /// # use periodical::intervals::relative::{RelativeBoundPair, RelativeFiniteBoundPosition};
    /// let abs_interval = AbsoluteBoundPair::new(
    ///     AbsoluteFiniteBoundPosition::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsoluteFiniteBoundPosition::new(
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
    ///         RelativeFiniteBoundPosition::new(SignedDuration::from_hours(8),).to_start_bound(),
    ///         RelativeFiniteBoundPosition::new(SignedDuration::from_hours(16),).to_end_bound(),
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
    RelativeFiniteBoundPosition,
    RelativeStartBound,
    RelativeEndBound,
    RelativeBoundPair,
    EmptiableRelativeBoundPair,
    BoundedRelativeInterval,
    HalfBoundedRelativeInterval,
    RelativeInterval,
    EmptiableRelativeInterval,
]);

impl ToRelative for AbsoluteFiniteBoundPosition {
    type RelativeType = RelativeFiniteBoundPosition;

    fn to_relative(&self, reference: Timestamp) -> Self::RelativeType {
        RelativeFiniteBoundPosition::new_with_inclusivity(self.time().duration_since(reference), self.inclusivity())
    }
}

impl ToRelative for AbsoluteStartBound {
    type RelativeType = RelativeStartBound;

    fn to_relative(&self, reference: Timestamp) -> Self::RelativeType {
        match self {
            AbsoluteStartBound::InfinitePast => RelativeStartBound::InfinitePast,
            AbsoluteStartBound::Finite(absolute_finite) => RelativeFiniteBoundPosition::new_with_inclusivity(
                absolute_finite.pos().time().duration_since(reference),
                absolute_finite.pos().inclusivity(),
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
            AbsoluteEndBound::Finite(absolute_finite) => RelativeFiniteBoundPosition::new_with_inclusivity(
                absolute_finite.pos().time().duration_since(reference),
                absolute_finite.pos().inclusivity(),
            )
            .to_end_bound(),
        }
    }
}

impl ToRelative for AbsoluteBoundPair {
    type RelativeType = RelativeBoundPair;

    fn to_relative(&self, reference: Timestamp) -> Self::RelativeType {
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
        BoundedRelativeInterval::new_from_offsets_and_inclusivities(
            self.start_time().duration_since(reference),
            self.start_inclusivity(),
            self.end_time().duration_since(reference),
            self.end_inclusivity(),
        )
    }
}

impl ToRelative for HalfBoundedAbsoluteInterval {
    type RelativeType = HalfBoundedRelativeInterval;

    fn to_relative(&self, reference: Timestamp) -> Self::RelativeType {
        HalfBoundedRelativeInterval::new_from_offset_and_inclusivity(
            self.reference_time().duration_since(reference),
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

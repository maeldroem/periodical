//! Relativity conversion
//!
//! Conversion from absolute to relative is defined by [`ToRel`].
//! Its opposite, conversion from relative to absolute, is defined by
//! [`ToAbs`].

use jiff::Timestamp;

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HasAbsBoundPair,
};
use crate::intervals::meta::{HasBoundInclusivity, HasOpeningDirection};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    EmptiableRelInterval,
    HalfBoundedRelInterval,
    HasRelBoundPair,
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelInterval,
    RelStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

macro_rules! to_absolute_impl_reflective {
    ([$($implementor:ty),* $(,)?]) => {
        $(
            impl ToAbsolute for $implementor {
                type AbsType = Self;

                fn to_absolute(&self, _reference: Timestamp) -> Self::AbsType {
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
                type RelType = Self;

                fn to_relative(&self, _reference: Timestamp) -> Self::RelType {
                    self.clone()
                }
            }
        )*
    };
}

/// Conversion into absolute
///
/// This trait is reflexive: absolute structures should implement
/// [`ToAbs`].
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::{SignedDuration, Zoned};
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::ops::relativity_conversion::ToAbsolute;
/// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
/// let rel_interval = RelBoundPair::new(
///     RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound(),
///     RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_end_bound(),
/// );
///
/// assert_eq!(
///     rel_interval.to_absolute(
///         "2025-01-01 00:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp()
///     ),
///     AbsBoundPair::new(
///         AbsFiniteBoundPos::new(
///             "2025-01-01 08:00:00[Europe/Oslo]"
///                 .parse::<Zoned>()?
///                 .timestamp(),
///         )
///         .to_start_bound(),
///         AbsFiniteBoundPos::new(
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
    type AbsType;

    /// Converts into absolute
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::{SignedDuration, Zoned};
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::ops::relativity_conversion::ToAbsolute;
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// let rel_interval = RelBoundPair::new(
    ///     RelFiniteBoundPos::new(SignedDuration::from_hours(8)).to_start_bound(),
    ///     RelFiniteBoundPos::new(SignedDuration::from_hours(16)).to_end_bound(),
    /// );
    ///
    /// assert_eq!(
    ///     rel_interval.to_absolute(
    ///         "2025-01-01 00:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp()
    ///     ),
    ///     AbsBoundPair::new(
    ///         AbsFiniteBoundPos::new(
    ///             "2025-01-01 08:00:00[Europe/Oslo]"
    ///                 .parse::<Zoned>()?
    ///                 .timestamp(),
    ///         )
    ///         .to_start_bound(),
    ///         AbsFiniteBoundPos::new(
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
    fn to_absolute(&self, reference: Timestamp) -> Self::AbsType;
}

to_absolute_impl_reflective!([
    UnboundedInterval,
    EmptyInterval,
    AbsFiniteBoundPos,
    AbsStartBound,
    AbsEndBound,
    AbsBoundPair,
    EmptiableAbsBoundPair,
    BoundedAbsInterval,
    HalfBoundedAbsInterval,
    AbsInterval,
    EmptiableAbsInterval,
]);

impl ToAbsolute for RelFiniteBoundPos {
    type AbsType = AbsFiniteBoundPos;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsType {
        AbsFiniteBoundPos::new_with_inclusivity(reference + self.offset(), self.inclusivity())
    }
}

impl ToAbsolute for RelStartBound {
    type AbsType = AbsStartBound;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsType {
        match self {
            RelStartBound::InfinitePast => AbsStartBound::InfinitePast,
            RelStartBound::Finite(relative_finite) => AbsFiniteBoundPos::new_with_inclusivity(
                reference + relative_finite.pos().offset(),
                relative_finite.pos().inclusivity(),
            )
            .to_start_bound(),
        }
    }
}

impl ToAbsolute for RelEndBound {
    type AbsType = AbsEndBound;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsType {
        match self {
            RelEndBound::InfiniteFuture => AbsEndBound::InfiniteFuture,
            RelEndBound::Finite(relative_finite) => AbsFiniteBoundPos::new_with_inclusivity(
                reference + relative_finite.pos().offset(),
                relative_finite.pos().inclusivity(),
            )
            .to_end_bound(),
        }
    }
}

impl ToAbsolute for RelBoundPair {
    type AbsType = AbsBoundPair;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsType {
        AbsBoundPair::new(
            self.rel_start().to_absolute(reference),
            self.rel_end().to_absolute(reference),
        )
    }
}

impl ToAbsolute for EmptiableRelBoundPair {
    type AbsType = EmptiableAbsBoundPair;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsType {
        match self {
            Self::Empty => EmptiableAbsBoundPair::Empty,
            Self::Bound(abs_bound_pair) => EmptiableAbsBoundPair::Bound(abs_bound_pair.to_absolute(reference)),
        }
    }
}

impl ToAbsolute for BoundedRelInterval {
    type AbsType = BoundedAbsInterval;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsType {
        BoundedAbsInterval::unchecked_from_times_incl(
            reference + self.start_offset(),
            self.start_inclusivity(),
            reference + self.end_offset(),
            self.end_inclusivity(),
        )
    }
}

impl ToAbsolute for HalfBoundedRelInterval {
    type AbsType = HalfBoundedAbsInterval;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsType {
        HalfBoundedAbsInterval::new_from_time_and_inclusivity(
            reference + self.reference_offset(),
            self.reference_inclusivity(),
            self.opening_direction(),
        )
    }
}

impl ToAbsolute for RelInterval {
    type AbsType = AbsInterval;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsType {
        match self {
            Self::Bounded(bounded) => AbsInterval::Bounded(bounded.to_absolute(reference)),
            Self::HalfBounded(half_bounded) => AbsInterval::HalfBounded(half_bounded.to_absolute(reference)),
            Self::Unbounded(unbounded) => AbsInterval::Unbounded(unbounded.to_absolute(reference)),
        }
    }
}

impl ToAbsolute for EmptiableRelInterval {
    type AbsType = EmptiableAbsInterval;

    fn to_absolute(&self, reference: Timestamp) -> Self::AbsType {
        match self {
            Self::Bound(interval) => EmptiableAbsInterval::Bound(interval.to_absolute(reference)),
            Self::Empty(empty) => EmptiableAbsInterval::Empty(empty.to_absolute(reference)),
        }
    }
}

/// Conversion into relative
///
/// This trait is reflexive: relative structures should implement
/// [`ToRel`].
///
/// # Examples
///
/// ```
/// # use std::error::Error;
/// # use jiff::{SignedDuration, Zoned};
/// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
/// # use periodical::intervals::ops::relativity_conversion::ToRelative;
/// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
/// let abs_interval = AbsBoundPair::new(
///     AbsFiniteBoundPos::new(
///         "2025-01-01 08:00:00[Europe/Oslo]"
///             .parse::<Zoned>()?
///             .timestamp(),
///     )
///     .to_start_bound(),
///     AbsFiniteBoundPos::new(
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
///     RelBoundPair::new(
///         RelFiniteBoundPos::new(SignedDuration::from_hours(8),).to_start_bound(),
///         RelFiniteBoundPos::new(SignedDuration::from_hours(16),).to_end_bound(),
///     ),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait ToRelative {
    type RelType;

    /// Converts into relative
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::{SignedDuration, Zoned};
    /// # use periodical::intervals::absolute::{AbsBoundPair, AbsFiniteBoundPos};
    /// # use periodical::intervals::ops::relativity_conversion::ToRelative;
    /// # use periodical::intervals::relative::{RelBoundPair, RelFiniteBoundPos};
    /// let abs_interval = AbsBoundPair::new(
    ///     AbsFiniteBoundPos::new(
    ///         "2025-01-01 08:00:00[Europe/Oslo]"
    ///             .parse::<Zoned>()?
    ///             .timestamp(),
    ///     )
    ///     .to_start_bound(),
    ///     AbsFiniteBoundPos::new(
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
    ///     RelBoundPair::new(
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(8),).to_start_bound(),
    ///         RelFiniteBoundPos::new(SignedDuration::from_hours(16),).to_end_bound(),
    ///     ),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    fn to_relative(&self, reference: Timestamp) -> Self::RelType;
}

to_relative_impl_reflective!([
    UnboundedInterval,
    EmptyInterval,
    RelFiniteBoundPos,
    RelStartBound,
    RelEndBound,
    RelBoundPair,
    EmptiableRelBoundPair,
    BoundedRelInterval,
    HalfBoundedRelInterval,
    RelInterval,
    EmptiableRelInterval,
]);

impl ToRelative for AbsFiniteBoundPos {
    type RelType = RelFiniteBoundPos;

    fn to_relative(&self, reference: Timestamp) -> Self::RelType {
        RelFiniteBoundPos::new_with_inclusivity(self.time().duration_since(reference), self.inclusivity())
    }
}

impl ToRelative for AbsStartBound {
    type RelType = RelStartBound;

    fn to_relative(&self, reference: Timestamp) -> Self::RelType {
        match self {
            AbsStartBound::InfinitePast => RelStartBound::InfinitePast,
            AbsStartBound::Finite(absolute_finite) => RelFiniteBoundPos::new_with_inclusivity(
                absolute_finite.pos().time().duration_since(reference),
                absolute_finite.pos().inclusivity(),
            )
            .to_start_bound(),
        }
    }
}

impl ToRelative for AbsEndBound {
    type RelType = RelEndBound;

    fn to_relative(&self, reference: Timestamp) -> Self::RelType {
        match self {
            AbsEndBound::InfiniteFuture => RelEndBound::InfiniteFuture,
            AbsEndBound::Finite(absolute_finite) => RelFiniteBoundPos::new_with_inclusivity(
                absolute_finite.pos().time().duration_since(reference),
                absolute_finite.pos().inclusivity(),
            )
            .to_end_bound(),
        }
    }
}

impl ToRelative for AbsBoundPair {
    type RelType = RelBoundPair;

    fn to_relative(&self, reference: Timestamp) -> Self::RelType {
        RelBoundPair::new(
            self.abs_start().to_relative(reference),
            self.abs_end().to_relative(reference),
        )
    }
}

impl ToRelative for EmptiableAbsBoundPair {
    type RelType = EmptiableRelBoundPair;

    fn to_relative(&self, reference: Timestamp) -> Self::RelType {
        match self {
            Self::Empty => EmptiableRelBoundPair::Empty,
            Self::Bound(abs_bound_pair) => EmptiableRelBoundPair::Bound(abs_bound_pair.to_relative(reference)),
        }
    }
}

impl ToRelative for BoundedAbsInterval {
    type RelType = BoundedRelInterval;

    fn to_relative(&self, reference: Timestamp) -> Self::RelType {
        BoundedRelInterval::from_offsets_incl(
            self.start_time().duration_since(reference),
            self.start_inclusivity(),
            self.end_time().duration_since(reference),
            self.end_inclusivity(),
        )
    }
}

impl ToRelative for HalfBoundedAbsInterval {
    type RelType = HalfBoundedRelInterval;

    fn to_relative(&self, reference: Timestamp) -> Self::RelType {
        HalfBoundedRelInterval::new_from_offset_and_inclusivity(
            self.reference_time().duration_since(reference),
            self.reference_inclusivity(),
            self.opening_direction(),
        )
    }
}

impl ToRelative for AbsInterval {
    type RelType = RelInterval;

    fn to_relative(&self, reference: Timestamp) -> Self::RelType {
        match self {
            Self::Bounded(bounded) => RelInterval::Bounded(bounded.to_relative(reference)),
            Self::HalfBounded(half_bounded) => RelInterval::HalfBounded(half_bounded.to_relative(reference)),
            Self::Unbounded(unbounded) => RelInterval::Unbounded(unbounded.to_relative(reference)),
        }
    }
}

impl ToRelative for EmptiableAbsInterval {
    type RelType = EmptiableRelInterval;

    fn to_relative(&self, reference: Timestamp) -> Self::RelType {
        match self {
            Self::Bound(interval) => EmptiableRelInterval::Bound(interval.to_relative(reference)),
            Self::Empty(empty) => EmptiableRelInterval::Empty(empty.to_relative(reference)),
        }
    }
}

//! Relativity conversion
//!
//! Conversion from absolute to relative is defined by [`ToRelative`].
//! Its opposite, conversion from relative to absolute, is defined by [`ToAbsolute`].

use chrono::{DateTime, Utc};

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteInterval, AbsoluteStartBound,
    BoundedAbsoluteInterval, EmptiableAbsoluteBounds, HalfBoundedAbsoluteInterval, HasAbsoluteBounds,
};
use crate::intervals::meta::HasBoundInclusivity;
use crate::intervals::relative::{
    BoundedRelativeInterval, EmptiableRelativeBounds, HalfBoundedRelativeInterval, HasRelativeBounds, RelativeBounds,
    RelativeEndBound, RelativeFiniteBound, RelativeInterval, RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

/// Conversion into absolute
///
/// This trait is reflexive: absolute structures should implement [`ToAbsolute`].
///
/// # Examples
///
/// ```
/// # use chrono::{DateTime, Duration, Utc};
/// # use periodical::intervals::absolute::{
/// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
/// # };
/// # use periodical::intervals::ops::relativity_conversion::ToAbsolute;
/// # use periodical::intervals::relative::{
/// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
/// # };
/// let rel_interval = RelativeBounds::new(
///     RelativeStartBound::Finite(RelativeFiniteBound::new(
///         Duration::hours(8),
///     )),
///     RelativeEndBound::Finite(RelativeFiniteBound::new(
///         Duration::hours(16),
///     )),
/// );
///
/// assert_eq!(
///     rel_interval.to_absolute("2025-01-01 00:00:00Z".parse::<DateTime<Utc>>()?),
///     AbsoluteBounds::new(
///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///         )),
///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///             "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
///         )),
///     ),
/// );
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
pub trait ToAbsolute {
    type AbsoluteType;

    /// Converts into absolute
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Duration, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::ops::relativity_conversion::ToAbsolute;
    /// # use periodical::intervals::relative::{
    /// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
    /// # };
    /// let rel_interval = RelativeBounds::new(
    ///     RelativeStartBound::Finite(RelativeFiniteBound::new(
    ///         Duration::hours(8),
    ///     )),
    ///     RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///         Duration::hours(16),
    ///     )),
    /// );
    ///
    /// assert_eq!(
    ///     rel_interval.to_absolute("2025-01-01 00:00:00Z".parse::<DateTime<Utc>>()?),
    ///     AbsoluteBounds::new(
    ///         AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///         AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///             "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    ///         )),
    ///     ),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType;
}

impl ToAbsolute for UnboundedInterval {
    type AbsoluteType = UnboundedInterval;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        *self
    }
}

impl ToAbsolute for EmptyInterval {
    type AbsoluteType = EmptyInterval;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        *self
    }
}

impl ToAbsolute for AbsoluteFiniteBound {
    type AbsoluteType = Self;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        *self
    }
}

impl ToAbsolute for AbsoluteStartBound {
    type AbsoluteType = AbsoluteStartBound;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        *self
    }
}

impl ToAbsolute for AbsoluteEndBound {
    type AbsoluteType = AbsoluteEndBound;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        *self
    }
}

impl ToAbsolute for AbsoluteBounds {
    type AbsoluteType = AbsoluteBounds;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        self.clone()
    }
}

impl ToAbsolute for EmptiableAbsoluteBounds {
    type AbsoluteType = Self;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        self.clone()
    }
}

impl ToAbsolute for BoundedAbsoluteInterval {
    type AbsoluteType = BoundedAbsoluteInterval;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        self.clone()
    }
}

impl ToAbsolute for HalfBoundedAbsoluteInterval {
    type AbsoluteType = HalfBoundedAbsoluteInterval;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        self.clone()
    }
}

impl ToAbsolute for AbsoluteInterval {
    type AbsoluteType = AbsoluteInterval;

    fn to_absolute(&self, _reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        self.clone()
    }
}

impl ToAbsolute for RelativeFiniteBound {
    type AbsoluteType = AbsoluteFiniteBound;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        AbsoluteFiniteBound::new_with_inclusivity(reference_time + self.offset(), self.inclusivity())
    }
}

impl ToAbsolute for RelativeStartBound {
    type AbsoluteType = AbsoluteStartBound;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        match self {
            RelativeStartBound::InfinitePast => AbsoluteStartBound::InfinitePast,
            RelativeStartBound::Finite(relative_finite) => {
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    reference_time + relative_finite.offset(),
                    relative_finite.inclusivity(),
                ))
            },
        }
    }
}

impl ToAbsolute for RelativeEndBound {
    type AbsoluteType = AbsoluteEndBound;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        match self {
            RelativeEndBound::InfiniteFuture => AbsoluteEndBound::InfiniteFuture,
            RelativeEndBound::Finite(relative_finite) => {
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    reference_time + relative_finite.offset(),
                    relative_finite.inclusivity(),
                ))
            },
        }
    }
}

impl ToAbsolute for RelativeBounds {
    type AbsoluteType = AbsoluteBounds;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        AbsoluteBounds::new(
            self.rel_start().to_absolute(reference_time),
            self.rel_end().to_absolute(reference_time),
        )
    }
}

impl ToAbsolute for EmptiableRelativeBounds {
    type AbsoluteType = EmptiableAbsoluteBounds;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        match self {
            Self::Empty => EmptiableAbsoluteBounds::Empty,
            Self::Bound(abs_bounds) => EmptiableAbsoluteBounds::Bound(abs_bounds.to_absolute(reference_time)),
        }
    }
}

impl ToAbsolute for BoundedRelativeInterval {
    type AbsoluteType = BoundedAbsoluteInterval;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        BoundedAbsoluteInterval::unchecked_new_with_inclusivity(
            reference_time + self.offset(),
            self.from_inclusivity(),
            reference_time + self.offset() + self.length(),
            self.to_inclusivity(),
        )
    }
}

impl ToAbsolute for HalfBoundedRelativeInterval {
    type AbsoluteType = HalfBoundedAbsoluteInterval;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            reference_time + self.reference_offset(),
            self.reference_inclusivity(),
            self.opening_direction(),
        )
    }
}

impl ToAbsolute for RelativeInterval {
    type AbsoluteType = AbsoluteInterval;

    fn to_absolute(&self, reference_time: DateTime<Utc>) -> Self::AbsoluteType {
        match self {
            Self::Bounded(bounded) => AbsoluteInterval::Bounded(bounded.to_absolute(reference_time)),
            Self::HalfBounded(half_bounded) => AbsoluteInterval::HalfBounded(half_bounded.to_absolute(reference_time)),
            Self::Unbounded(unbounded) => AbsoluteInterval::Unbounded(unbounded.to_absolute(reference_time)),
            Self::Empty(empty) => AbsoluteInterval::Empty(empty.to_absolute(reference_time)),
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
/// # use chrono::{DateTime, Duration, Utc};
/// # use periodical::intervals::absolute::{
/// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
/// # };
/// # use periodical::intervals::ops::relativity_conversion::ToRelative;
/// # use periodical::intervals::relative::{
/// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
/// # };
/// let abs_interval = AbsoluteBounds::new(
///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
/// );
///
/// assert_eq!(
///     abs_interval.to_relative("2025-01-01 00:00:00Z".parse::<DateTime<Utc>>()?),
///     RelativeBounds::new(
///         RelativeStartBound::Finite(RelativeFiniteBound::new(
///             Duration::hours(8),
///         )),
///         RelativeEndBound::Finite(RelativeFiniteBound::new(
///             Duration::hours(16),
///         )),
///     ),
/// );
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
pub trait ToRelative {
    type RelativeType;

    /// Converts into relative
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Duration, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::ops::relativity_conversion::ToRelative;
    /// # use periodical::intervals::relative::{
    /// #     RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
    /// # };
    /// let abs_interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 16:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// assert_eq!(
    ///     abs_interval.to_relative("2025-01-01 00:00:00Z".parse::<DateTime<Utc>>()?),
    ///     RelativeBounds::new(
    ///         RelativeStartBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(8),
    ///         )),
    ///         RelativeEndBound::Finite(RelativeFiniteBound::new(
    ///             Duration::hours(16),
    ///         )),
    ///     ),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    #[must_use]
    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType;
}

impl ToRelative for UnboundedInterval {
    type RelativeType = UnboundedInterval;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        *self
    }
}

impl ToRelative for EmptyInterval {
    type RelativeType = EmptyInterval;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        *self
    }
}

impl ToRelative for AbsoluteFiniteBound {
    type RelativeType = RelativeFiniteBound;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        RelativeFiniteBound::new_with_inclusivity(self.time() - reference_time, self.inclusivity())
    }
}

impl ToRelative for AbsoluteStartBound {
    type RelativeType = RelativeStartBound;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        match self {
            AbsoluteStartBound::InfinitePast => RelativeStartBound::InfinitePast,
            AbsoluteStartBound::Finite(absolute_finite) => {
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    absolute_finite.time() - reference_time,
                    absolute_finite.inclusivity(),
                ))
            },
        }
    }
}

impl ToRelative for AbsoluteEndBound {
    type RelativeType = RelativeEndBound;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        match self {
            AbsoluteEndBound::InfiniteFuture => RelativeEndBound::InfiniteFuture,
            AbsoluteEndBound::Finite(absolute_finite) => {
                RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    absolute_finite.time() - reference_time,
                    absolute_finite.inclusivity(),
                ))
            },
        }
    }
}

impl ToRelative for AbsoluteBounds {
    type RelativeType = RelativeBounds;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        RelativeBounds::new(
            self.abs_start().to_relative(reference_time),
            self.abs_end().to_relative(reference_time),
        )
    }
}

impl ToRelative for EmptiableAbsoluteBounds {
    type RelativeType = EmptiableRelativeBounds;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        match self {
            Self::Empty => EmptiableRelativeBounds::Empty,
            Self::Bound(abs_bounds) => EmptiableRelativeBounds::Bound(abs_bounds.to_relative(reference_time)),
        }
    }
}

impl ToRelative for BoundedAbsoluteInterval {
    type RelativeType = BoundedRelativeInterval;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        BoundedRelativeInterval::new_with_inclusivity(
            self.from_time() - reference_time,
            self.from_inclusivity(),
            self.to_time() - self.from_time(),
            self.to_inclusivity(),
        )
    }
}

impl ToRelative for HalfBoundedAbsoluteInterval {
    type RelativeType = HalfBoundedRelativeInterval;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        HalfBoundedRelativeInterval::new_with_inclusivity(
            self.reference_time() - reference_time,
            self.reference_inclusivity(),
            self.opening_direction(),
        )
    }
}

impl ToRelative for AbsoluteInterval {
    type RelativeType = RelativeInterval;

    fn to_relative(&self, reference_time: DateTime<Utc>) -> Self::RelativeType {
        match self {
            Self::Bounded(bounded) => RelativeInterval::Bounded(bounded.to_relative(reference_time)),
            Self::HalfBounded(half_bounded) => RelativeInterval::HalfBounded(half_bounded.to_relative(reference_time)),
            Self::Unbounded(unbounded) => RelativeInterval::Unbounded(unbounded.to_relative(reference_time)),
            Self::Empty(empty) => RelativeInterval::Empty(empty.to_relative(reference_time)),
        }
    }
}

impl ToRelative for RelativeFiniteBound {
    type RelativeType = Self;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        *self
    }
}

impl ToRelative for RelativeStartBound {
    type RelativeType = RelativeStartBound;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        *self
    }
}

impl ToRelative for RelativeEndBound {
    type RelativeType = RelativeEndBound;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        *self
    }
}

impl ToRelative for RelativeBounds {
    type RelativeType = RelativeBounds;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
    }
}

impl ToRelative for EmptiableRelativeBounds {
    type RelativeType = Self;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
    }
}

impl ToRelative for BoundedRelativeInterval {
    type RelativeType = BoundedRelativeInterval;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
    }
}

impl ToRelative for HalfBoundedRelativeInterval {
    type RelativeType = HalfBoundedRelativeInterval;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
    }
}

impl ToRelative for RelativeInterval {
    type RelativeType = RelativeInterval;

    fn to_relative(&self, _reference_time: DateTime<Utc>) -> Self::RelativeType {
        self.clone()
    }
}

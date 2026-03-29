//! Interval cutting
//!
//! Cutting an interval results in two split intervals, if the position of the
//! cut is within the interval, that is. The type of gap created by the cut is
//! chosen by the given [`CutType`], which describes the new inclusivities
//! of the now-split intervals for where the cut has occurred.
//!
//! Cutting an interval at a start/end will work only if the actual bound is
//! inclusive and the [`CutType`] also defines that this part of the cut should
//! be inclusive, resulting in an interval representing a single point in time.
//! If those requirements are not met, the operation will result in
//! [`CutResult::Uncut`], as cutting would create an illegal interval.
//!
//! If you are looking to make a "cut" with a non-zero duration gap,
//! see [`Differentiable`](crate::intervals::ops::set_ops::Differentiable).
//!
//! # Examples
//!
//! ## Cutting an interval in two
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::cut::{CutResult, Cuttable, CutType};
//! let interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 16:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! let cut_type = CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive);
//! let at = "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?;
//!
//! assert_eq!(
//!     interval.cut_at(at, cut_type),
//!     CutResult::Cut(
//!         AbsoluteBoundPair::new(
//!             AbsoluteFiniteBound::new(
//!                 "2025-01-01 08:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp()
//!             )
//!             .to_start_bound(),
//!             AbsoluteFiniteBound::new_with_inclusivity(
//!                 "2025-01-01 12:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp(),
//!                 BoundInclusivity::Exclusive,
//!             )
//!             .to_end_bound(),
//!         ),
//!         AbsoluteBoundPair::new(
//!             AbsoluteFiniteBound::new_with_inclusivity(
//!                 "2025-01-01 12:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp(),
//!                 BoundInclusivity::Exclusive,
//!             )
//!             .to_start_bound(),
//!             AbsoluteFiniteBound::new(
//!                 "2025-01-01 16:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp(),
//!             )
//!             .to_end_bound(),
//!         ),
//!     ),
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```
//!
//! ## Cutting at one end
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::cut::{CutResult, Cuttable, CutType};
//! let interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 16:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! let cut_type = CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive);
//! let at = "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?;
//!
//! assert_eq!(
//!     interval.cut_at(at, cut_type),
//!     CutResult::Cut(
//!         AbsoluteBoundPair::new(
//!             AbsoluteFiniteBound::new(
//!                 "2025-01-01 08:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp()
//!             )
//!             .to_start_bound(),
//!             AbsoluteFiniteBound::new_with_inclusivity(
//!                 "2025-01-01 16:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp(),
//!                 BoundInclusivity::Exclusive,
//!             )
//!             .to_end_bound(),
//!         ),
//!         AbsoluteBoundPair::new(
//!             AbsoluteFiniteBound::new(
//!                 "2025-01-01 16:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp(),
//!             )
//!             .to_start_bound(),
//!             AbsoluteFiniteBound::new(
//!                 "2025-01-01 16:00:00[Europe/Oslo]"
//!                     .parse::<Zoned>()?
//!                     .timestamp(),
//!             )
//!             .to_end_bound(),
//!         ),
//!     ),
//! );
//! # Ok::<(), Box<dyn Error>>(())
//! ```
//!
//! ## Trying to cut a bound into an illegal interval
//!
//! ```
//! # use std::error::Error;
//! # use jiff::Zoned;
//! # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
//! # use periodical::intervals::meta::BoundInclusivity;
//! # use periodical::intervals::ops::cut::{CutResult, Cuttable, CutType};
//! let interval = AbsoluteBoundPair::new(
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 08:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_start_bound(),
//!     AbsoluteFiniteBound::new(
//!         "2025-01-01 16:00:00[Europe/Oslo]"
//!             .parse::<Zoned>()?
//!             .timestamp(),
//!     )
//!     .to_end_bound(),
//! );
//!
//! let cut_type = CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive);
//! let at = "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?;
//!
//! assert_eq!(interval.cut_at(at, cut_type), CutResult::Uncut,);
//! # Ok::<(), Box<dyn Error>>(())
//! ```

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use jiff::{SignedDuration, Timestamp};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use super::point_containment::CanPositionPointContainment;
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
    HasEmptiableAbsoluteBoundPair,
    check_absolute_bound_pair_for_interval_creation,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    EmptiableRelativeInterval,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeInterval,
    RelativeStartBound,
    check_relative_bound_pair_for_interval_creation,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

/// Cut type
///
/// Describes what [`BoundInclusivity`]s should be put at the place of the cut.
///
/// The first element describes the [`BoundInclusivity`] to put on the past part
/// of the cut, the second element describes the [`BoundInclusivity`] to put on
/// the future part of the cut.
///
/// For example, `CutType::new(BoundInclusivity::Inclusive,
/// BoundInclusivity::Exclusive)`, will cut an interval such that the first cut
/// part will end with an inclusive bound at the position
/// given to [`Cuttable::cut_at`], and the second part will start with an
/// exclusive bound at the same position.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub struct CutType(BoundInclusivity, BoundInclusivity);

impl CutType {
    /// Creates a new [`CutType`]
    #[must_use]
    pub fn new(past_inclusivity: BoundInclusivity, future_inclusivity: BoundInclusivity) -> Self {
        CutType(past_inclusivity, future_inclusivity)
    }

    /// Returns the [`BoundInclusivity`] for the past side
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::cut::CutType;
    /// let cut_type = CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     cut_type.past_bound_inclusivity(),
    ///     BoundInclusivity::Inclusive
    /// );
    /// ```
    #[must_use]
    pub fn past_bound_inclusivity(&self) -> BoundInclusivity {
        self.0
    }

    /// Returns the [`BoundInclusivity`] for the future side
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::cut::CutType;
    /// let cut_type = CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     cut_type.future_bound_inclusivity(),
    ///     BoundInclusivity::Exclusive
    /// );
    /// ```
    #[must_use]
    pub fn future_bound_inclusivity(&self) -> BoundInclusivity {
        self.1
    }

    /// Returns a [`CutType`] with opposite inclusivities
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::cut::CutType;
    /// let cut_type = CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive);
    ///
    /// assert_eq!(
    ///     cut_type.opposite(),
    ///     CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive),
    /// );
    /// ```
    #[must_use]
    pub fn opposite(&self) -> Self {
        CutType::new(self.0.opposite(), self.1.opposite())
    }
}

impl From<(BoundInclusivity, BoundInclusivity)> for CutType {
    fn from((past_inclusivity, future_inclusivity): (BoundInclusivity, BoundInclusivity)) -> Self {
        CutType::new(past_inclusivity, future_inclusivity)
    }
}

/// Result of a [cut](Cuttable)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum CutResult<T> {
    /// Uncut result
    ///
    /// The cutting point is either outside the given interval, or would have
    /// created an illegal interval.
    Uncut,
    /// Cut result
    ///
    /// The cut was successful, the variant contains the two cut parts.
    ///
    /// The cut parts are always in chronological order, since a single interval
    /// can't be described backwards.
    Cut(T, T),
}

impl<T> CutResult<T> {
    /// Whether it is of the [`Uncut`](CutResult::Uncut) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::cut::CutResult;
    /// assert!(CutResult::<()>::Uncut.is_uncut());
    /// assert!(!CutResult::<()>::Cut((), ()).is_uncut());
    /// ```
    #[must_use]
    pub fn is_uncut(&self) -> bool {
        matches!(self, CutResult::Uncut)
    }

    /// Whether it is of the [`Cut`](CutResult::Cut) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::cut::CutResult;
    /// assert!(CutResult::<()>::Cut((), ()).is_cut());
    /// assert!(!CutResult::<()>::Uncut.is_cut());
    /// ```
    #[must_use]
    pub fn is_cut(&self) -> bool {
        matches!(self, CutResult::Cut(..))
    }

    /// Returns the content of the [`Cut`](CutResult::Cut) variant
    ///
    /// Consumes `self` and puts the content of the [`Cut`](CutResult::Cut)
    /// variant in an [`Option`]. If instead `self` is another variant, the
    /// method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::cut::CutResult;
    /// assert_eq!(CutResult::<u8>::Cut(10, 20).cut(), Some((10, 20)));
    /// assert_eq!(CutResult::<u8>::Uncut.cut(), None);
    /// ```
    #[must_use]
    pub fn cut(self) -> Option<(T, T)> {
        match self {
            Self::Uncut => None,
            Self::Cut(a, b) => Some((a, b)),
        }
    }

    /// Maps the contents of the [`Cut`](CutResult::Cut) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::ops::cut::CutResult;
    /// assert_eq!(
    ///     CutResult::<u8>::Cut(10, 20).map_cut(|x, y| (x * 2, y * 3)),
    ///     CutResult::<u8>::Cut(20, 60),
    /// );
    /// ```
    #[must_use]
    pub fn map_cut<F, U>(self, mut f: F) -> CutResult<U>
    where
        F: FnMut(T, T) -> (U, U),
    {
        match self {
            Self::Uncut => CutResult::Uncut,
            Self::Cut(c1, c2) => {
                let mapped_cut = (f)(c1, c2);
                CutResult::Cut(mapped_cut.0, mapped_cut.1)
            },
        }
    }
}

/// Capacity to cut an interval
///
/// The generic type parameter `P` corresponds to the type used for positioning
/// the cut.
///
/// Cutting an interval results in two split intervals, if the position of the
/// cut is within the interval, that is. The type of gap created by the cut is
/// chosen by the given [`CutType`], which describes the new inclusivities
/// of the now-split intervals for where the cut has occurred.
///
/// Cutting an interval at a start/end point will work only if the actual bound
/// is inclusive and the [`CutType`] also defines that this part of the cut
/// should be inclusive, resulting in an interval representing a single point in
/// time. If those requirements are not met, the operation will result in
/// [`CutResult::Uncut`], as cutting would create an illegal interval.
///
/// If you are looking to make a "cut" with a non-zero duration gap,
/// see [`Differentiable`](crate::intervals::ops::set_ops::Differentiable).
///
/// # Examples
///
/// ## Cutting an interval in two
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::cut::{CutResult, Cuttable, CutType};
/// let interval = AbsoluteBoundPair::new(
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
/// let cut_type = CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive);
/// let at = "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?;
///
/// assert_eq!(
///     interval.cut_at(at, cut_type),
///     CutResult::Cut(
///         AbsoluteBoundPair::new(
///             AbsoluteFiniteBound::new(
///                 "2025-01-01 08:00:00[Europe/Oslo]"
///                     .parse::<Zoned>()?
///                     .timestamp()
///             )
///             .to_start_bound(),
///             AbsoluteFiniteBound::new_with_inclusivity(
///                 "2025-01-01 12:00:00[Europe/Oslo]"
///                     .parse::<Zoned>()?
///                     .timestamp(),
///                 BoundInclusivity::Exclusive,
///             )
///             .to_end_bound(),
///         ),
///         AbsoluteBoundPair::new(
///             AbsoluteFiniteBound::new_with_inclusivity(
///                 "2025-01-01 12:00:00[Europe/Oslo]"
///                     .parse::<Zoned>()?
///                     .timestamp(),
///                 BoundInclusivity::Exclusive,
///             )
///             .to_start_bound(),
///             AbsoluteFiniteBound::new(
///                 "2025-01-01 16:00:00[Europe/Oslo]"
///                     .parse::<Zoned>()?
///                     .timestamp(),
///             )
///             .to_end_bound(),
///         ),
///     ),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Cutting at one end
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::cut::{CutResult, Cuttable, CutType};
/// let interval = AbsoluteBoundPair::new(
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
/// let cut_type = CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive);
/// let at = "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?;
///
/// assert_eq!(
///     interval.cut_at(at, cut_type),
///     CutResult::Cut(
///         AbsoluteBoundPair::new(
///             AbsoluteFiniteBound::new(
///                 "2025-01-01 08:00:00[Europe/Oslo]"
///                     .parse::<Zoned>()?
///                     .timestamp()
///             )
///             .to_start_bound(),
///             AbsoluteFiniteBound::new_with_inclusivity(
///                 "2025-01-01 16:00:00[Europe/Oslo]"
///                     .parse::<Zoned>()?
///                     .timestamp(),
///                 BoundInclusivity::Exclusive,
///             )
///             .to_end_bound(),
///         ),
///         AbsoluteBoundPair::new(
///             AbsoluteFiniteBound::new(
///                 "2025-01-01 16:00:00[Europe/Oslo]"
///                     .parse::<Zoned>()?
///                     .timestamp(),
///             )
///             .to_start_bound(),
///             AbsoluteFiniteBound::new(
///                 "2025-01-01 16:00:00[Europe/Oslo]"
///                     .parse::<Zoned>()?
///                     .timestamp(),
///             )
///             .to_end_bound(),
///         ),
///     ),
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
///
/// ## Trying to cut a bound into an illegal interval
///
/// ```
/// # use std::error::Error;
/// # use jiff::Zoned;
/// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
/// # use periodical::intervals::meta::BoundInclusivity;
/// # use periodical::intervals::ops::cut::{CutResult, Cuttable, CutType};
/// let interval = AbsoluteBoundPair::new(
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
/// let cut_type = CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive);
/// let at = "2025-01-01 16:00:00[Europe/Oslo]".parse::<Zoned>()?;
///
/// assert_eq!(interval.cut_at(at, cut_type), CutResult::Uncut,);
/// # Ok::<(), Box<dyn Error>>(())
/// ```
pub trait Cuttable<P> {
    /// Output type
    type Output;

    /// Cuts the interval at the given position
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{AbsoluteBoundPair, AbsoluteFiniteBound};
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::cut::{CutResult, Cuttable, CutType};
    /// let interval = AbsoluteBoundPair::new(
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
    /// let cut_type = CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive);
    /// let at = "2025-01-01 12:00:00[Europe/Oslo]".parse::<Zoned>()?;
    ///
    /// assert_eq!(
    ///     interval.cut_at(at, cut_type),
    ///     CutResult::Cut(
    ///         AbsoluteBoundPair::new(
    ///             AbsoluteFiniteBound::new(
    ///                 "2025-01-01 08:00:00[Europe/Oslo]"
    ///                     .parse::<Zoned>()?
    ///                     .timestamp()
    ///             )
    ///             .to_start_bound(),
    ///             AbsoluteFiniteBound::new_with_inclusivity(
    ///                 "2025-01-01 12:00:00[Europe/Oslo]"
    ///                     .parse::<Zoned>()?
    ///                     .timestamp(),
    ///                 BoundInclusivity::Exclusive,
    ///             )
    ///             .to_end_bound(),
    ///         ),
    ///         AbsoluteBoundPair::new(
    ///             AbsoluteFiniteBound::new_with_inclusivity(
    ///                 "2025-01-01 12:00:00[Europe/Oslo]"
    ///                     .parse::<Zoned>()?
    ///                     .timestamp(),
    ///                 BoundInclusivity::Exclusive,
    ///             )
    ///             .to_start_bound(),
    ///             AbsoluteFiniteBound::new(
    ///                 "2025-01-01 16:00:00[Europe/Oslo]"
    ///                     .parse::<Zoned>()?
    ///                     .timestamp(),
    ///             )
    ///             .to_end_bound(),
    ///         ),
    ///     ),
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output>;
}

impl<P> Cuttable<P> for AbsoluteBoundPair
where
    P: Into<Timestamp>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_abs_bound_pair(self, position.into(), cut_type)
    }
}

impl<P> Cuttable<P> for EmptiableAbsoluteBoundPair
where
    P: Into<Timestamp>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_emptiable_abs_bound_pair(self, position.into(), cut_type)
    }
}

impl<P> Cuttable<P> for AbsoluteInterval
where
    P: Into<Timestamp>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_abs_bound_pair(&self.abs_bound_pair(), position.into(), cut_type)
            .map_cut(|c1, c2| (AbsoluteInterval::from(c1), AbsoluteInterval::from(c2)))
    }
}

impl<P> Cuttable<P> for EmptiableAbsoluteInterval
where
    P: Into<Timestamp>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_emptiable_abs_bound_pair(&self.emptiable_abs_bound_pair(), position.into(), cut_type)
            .map_cut(|c1, c2| (EmptiableAbsoluteInterval::from(c1), EmptiableAbsoluteInterval::from(c2)))
    }
}

impl<P> Cuttable<P> for BoundedAbsoluteInterval
where
    P: Into<Timestamp>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_bounded_abs_interval(self, position.into(), cut_type)
    }
}

impl<P> Cuttable<P> for HalfBoundedAbsoluteInterval
where
    P: Into<Timestamp>,
{
    type Output = AbsoluteInterval;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_abs_bound_pair(&self.abs_bound_pair(), position.into(), cut_type)
            .map_cut(|c1, c2| (AbsoluteInterval::from(c1), AbsoluteInterval::from(c2)))
    }
}

impl<P> Cuttable<P> for RelativeBoundPair
where
    P: Into<SignedDuration>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_rel_bound_pair(self, position.into(), cut_type)
    }
}

impl<P> Cuttable<P> for EmptiableRelativeBoundPair
where
    P: Into<SignedDuration>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_emptiable_rel_bound_pair(self, position.into(), cut_type)
    }
}

impl<P> Cuttable<P> for RelativeInterval
where
    P: Into<SignedDuration>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_rel_bound_pair(&self.rel_bound_pair(), position.into(), cut_type)
            .map_cut(|c1, c2| (RelativeInterval::from(c1), RelativeInterval::from(c2)))
    }
}

impl<P> Cuttable<P> for EmptiableRelativeInterval
where
    P: Into<SignedDuration>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_emptiable_rel_bound_pair(&self.emptiable_rel_bound_pair(), position.into(), cut_type)
            .map_cut(|c1, c2| (EmptiableRelativeInterval::from(c1), EmptiableRelativeInterval::from(c2)))
    }
}

impl<P> Cuttable<P> for BoundedRelativeInterval
where
    P: Into<SignedDuration>,
{
    type Output = Self;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_bounded_rel_interval(self, position.into(), cut_type)
    }
}

impl<P> Cuttable<P> for HalfBoundedRelativeInterval
where
    P: Into<SignedDuration>,
{
    type Output = RelativeInterval;

    fn cut_at(&self, position: P, cut_type: CutType) -> CutResult<Self::Output> {
        cut_rel_bound_pair(&self.rel_bound_pair(), position.into(), cut_type)
            .map_cut(|c1, c2| (RelativeInterval::from(c1), RelativeInterval::from(c2)))
    }
}

impl Cuttable<Timestamp> for UnboundedInterval {
    type Output = AbsoluteInterval;

    fn cut_at(&self, position: Timestamp, cut_type: CutType) -> CutResult<Self::Output> {
        cut_abs_bound_pair(&self.abs_bound_pair(), position, cut_type)
            .map_cut(|c1, c2| (AbsoluteInterval::from(c1), AbsoluteInterval::from(c2)))
    }
}

impl Cuttable<SignedDuration> for UnboundedInterval {
    type Output = RelativeInterval;

    fn cut_at(&self, position: SignedDuration, cut_type: CutType) -> CutResult<Self::Output> {
        cut_rel_bound_pair(&self.rel_bound_pair(), position, cut_type)
            .map_cut(|c1, c2| (RelativeInterval::from(c1), RelativeInterval::from(c2)))
    }
}

impl Cuttable<Timestamp> for EmptyInterval {
    type Output = ();

    fn cut_at(&self, _position: Timestamp, _cut_type: CutType) -> CutResult<Self::Output> {
        CutResult::Uncut
    }
}

impl Cuttable<SignedDuration> for EmptyInterval {
    type Output = ();

    fn cut_at(&self, _position: SignedDuration, _cut_type: CutType) -> CutResult<Self::Output> {
        CutResult::Uncut
    }
}

/// Cuts an [`AbsoluteBoundPair`] with a [`Timestamp`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn cut_abs_bound_pair(
    bounds: &AbsoluteBoundPair,
    at: Timestamp,
    cut_type: CutType,
) -> CutResult<AbsoluteBoundPair> {
    if !bounds.simple_contains_point(at) {
        return CutResult::Uncut;
    }

    let past_cut_end = AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        at,
        cut_type.past_bound_inclusivity(),
    ));
    let future_cut_start = AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        at,
        cut_type.future_bound_inclusivity(),
    ));

    if check_absolute_bound_pair_for_interval_creation(&bounds.start(), &past_cut_end).is_err()
        || check_absolute_bound_pair_for_interval_creation(&future_cut_start, &bounds.end()).is_err()
    {
        return CutResult::Uncut;
    }

    let mut past_split = bounds.clone();
    let mut future_split = bounds.clone();

    past_split.set_end(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        at,
        cut_type.past_bound_inclusivity(),
    )));

    future_split.set_start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
        at,
        cut_type.future_bound_inclusivity(),
    )));

    CutResult::Cut(past_split, future_split)
}

/// Cuts an [`EmptiableAbsoluteBoundPair`] with a [`Timestamp`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn cut_emptiable_abs_bound_pair(
    bounds: &EmptiableAbsoluteBoundPair,
    at: Timestamp,
    cut_type: CutType,
) -> CutResult<EmptiableAbsoluteBoundPair> {
    let EmptiableAbsoluteBoundPair::Bound(non_empty_bounds) = bounds else {
        // Empty bounds can't be cut
        return CutResult::Uncut;
    };

    cut_abs_bound_pair(non_empty_bounds, at, cut_type).map_cut(|c1, c2| {
        (
            EmptiableAbsoluteBoundPair::from(c1),
            EmptiableAbsoluteBoundPair::from(c2),
        )
    })
}

/// Cuts a [`BoundedAbsoluteInterval`] with a [`Timestamp`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn cut_bounded_abs_interval(
    interval: &BoundedAbsoluteInterval,
    at: Timestamp,
    cut_type: CutType,
) -> CutResult<BoundedAbsoluteInterval> {
    if !interval.simple_contains_point(at) {
        return CutResult::Uncut;
    }

    let past_cut_end = AbsoluteFiniteBound::new_with_inclusivity(at, cut_type.past_bound_inclusivity()).to_end_bound();

    let future_cut_start =
        AbsoluteFiniteBound::new_with_inclusivity(at, cut_type.future_bound_inclusivity()).to_start_bound();

    if check_absolute_bound_pair_for_interval_creation(&interval.abs_start(), &past_cut_end).is_err()
        || check_absolute_bound_pair_for_interval_creation(&future_cut_start, &interval.abs_end()).is_err()
    {
        return CutResult::Uncut;
    }

    let past_split = BoundedAbsoluteInterval::unchecked_new_with_inclusivity(
        interval.start(),
        interval.start_inclusivity(),
        at,
        cut_type.past_bound_inclusivity(),
    );

    let future_split = BoundedAbsoluteInterval::unchecked_new_with_inclusivity(
        at,
        cut_type.future_bound_inclusivity(),
        interval.end(),
        interval.end_inclusivity(),
    );

    CutResult::Cut(past_split, future_split)
}

/// Cuts a [`RelativeBoundPair`] with a [`Timestamp`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn cut_rel_bound_pair(
    bounds: &RelativeBoundPair,
    at: SignedDuration,
    cut_type: CutType,
) -> CutResult<RelativeBoundPair> {
    if !bounds.simple_contains_point(at) {
        return CutResult::Uncut;
    }

    let past_cut_end = RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        at,
        cut_type.past_bound_inclusivity(),
    ));
    let future_cut_start = RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        at,
        cut_type.future_bound_inclusivity(),
    ));

    if check_relative_bound_pair_for_interval_creation(&bounds.start(), &past_cut_end).is_err()
        || check_relative_bound_pair_for_interval_creation(&future_cut_start, &bounds.end()).is_err()
    {
        return CutResult::Uncut;
    }

    let mut past_split = bounds.clone();
    let mut future_split = bounds.clone();

    past_split.set_end(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        at,
        cut_type.past_bound_inclusivity(),
    )));

    future_split.set_start(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
        at,
        cut_type.future_bound_inclusivity(),
    )));

    CutResult::Cut(past_split, future_split)
}

/// Cuts an [`EmptiableRelativeBoundPair`] with a [`Timestamp`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn cut_emptiable_rel_bound_pair(
    bounds: &EmptiableRelativeBoundPair,
    at: SignedDuration,
    cut_type: CutType,
) -> CutResult<EmptiableRelativeBoundPair> {
    let EmptiableRelativeBoundPair::Bound(non_empty_bounds) = bounds else {
        // Empty bounds can't be cut
        return CutResult::Uncut;
    };

    cut_rel_bound_pair(non_empty_bounds, at, cut_type).map_cut(|c1, c2| {
        (
            EmptiableRelativeBoundPair::from(c1),
            EmptiableRelativeBoundPair::from(c2),
        )
    })
}

/// Cuts a [`BoundedRelativeInterval`] with a [`Timestamp`]
///
/// See [module documentation](self) for more info.
#[must_use]
pub fn cut_bounded_rel_interval(
    interval: &BoundedRelativeInterval,
    at: SignedDuration,
    cut_type: CutType,
) -> CutResult<BoundedRelativeInterval> {
    if !interval.simple_contains_point(at) {
        return CutResult::Uncut;
    }

    let past_cut_end = RelativeFiniteBound::new_with_inclusivity(at, cut_type.past_bound_inclusivity()).to_end_bound();

    let future_cut_start =
        RelativeFiniteBound::new_with_inclusivity(at, cut_type.future_bound_inclusivity()).to_start_bound();

    if check_relative_bound_pair_for_interval_creation(&interval.rel_start(), &past_cut_end).is_err()
        || check_relative_bound_pair_for_interval_creation(&future_cut_start, &interval.rel_end()).is_err()
    {
        return CutResult::Uncut;
    }

    let past_split = BoundedRelativeInterval::unchecked_new_with_inclusivity(
        interval.start(),
        interval.start_inclusivity(),
        at,
        cut_type.past_bound_inclusivity(),
    );

    let future_split = BoundedRelativeInterval::unchecked_new_with_inclusivity(
        at,
        cut_type.future_bound_inclusivity(),
        interval.end(),
        interval.end_inclusivity(),
    );

    CutResult::Cut(past_split, future_split)
}

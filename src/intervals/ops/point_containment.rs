//! Interval point containment positioning
//!
//! Given an interval and a point, positions the given point within the interval,
//! represented by [`PointContainmentPosition`].
//!
//! Since a point can fall on an [exclusive](BoundInclusivity::Exclusive) bound, this creates an ambiguity
//! that needs to be resolved.
//!
//! Using [`CanPositionPointContainment`] will return a [`PointContainmentPosition`],
//! which will then need to be disambiguated in order to obtain a concrete diagnostic of the containment.
//!
//! You can disambiguate a [`PointContainmentPosition`] using a [`PointContainmentRuleSet`] or a custom closure
//! by using [`PointContainmentPosition::disambiguate_using`].
//!
//! A disambiguated [`PointContainmentPosition`] is represented by [`DisambiguatedPointContainmentPosition`].
//!
//! Once disambiguated, the point containment position can be converted into a boolean decision of whether
//! the point is contained within the interval using [`PointContainmentRule`]s
//! with [`CanPositionPointContainment::contains_point`].
//!
//! # Examples
//!
//! ```
//! # use chrono::{DateTime, Utc};
//! # use periodical::intervals::absolute::{
//! #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
//! # };
//! # use periodical::intervals::ops::point_containment::CanPositionPointContainment;
//! let interval = AbsoluteBounds::new(
//!     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//!     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
//!         "2025-01-01 12:00:00Z".parse::<DateTime<Utc>>()?,
//!     )),
//! );
//!
//! let point = "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?;
//!
//! assert!(interval.simple_contains_point(point));
//! # Ok::<(), chrono::format::ParseError>(())
//! ```

use std::cmp::Ordering;
use std::convert::Infallible;

#[cfg(feature = "arbitrary")]
use arbitrary::Arbitrary;
use chrono::{DateTime, Duration, Utc};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteStartBound, EmptiableAbsoluteBounds, HalfBoundedAbsoluteInterval,
    HasAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{
    EmptiableRelativeBounds, HalfBoundedRelativeInterval, RelativeBounds, RelativeEndBound, RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::intervals::{AbsoluteInterval, BoundedAbsoluteInterval, BoundedRelativeInterval, RelativeInterval};

/// Point containment position
///
/// Defines where the point was found relative to the interval.
///
/// When [`point_position`](CanPositionPointContainment::point_containment_position) evaluates
/// the point containment position, it ignores the [inclusivities](BoundInclusivity) of the interval
/// and simply takes into account the position of its bounds.
///
/// If the point falls on one of those bounds, the [`BoundInclusivity`] of the bound is recorded within the variant,
/// which is only possible for [`OnStart`](PointContainmentPosition::OnStart)
/// and [`OnEnd`](PointContainmentPosition::OnEnd).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum PointContainmentPosition {
    /// Compared point is before the interval's start
    OutsideBefore,
    /// Compared point is after the interval's end
    OutsideAfter,
    /// Compared point is outside the interval
    ///
    /// This result is only possible when dealing with empty intervals
    Outside,
    /// Compared point is exactly on the start of the interval
    ///
    /// Since the point falls on a bound from the interval, it creates an ambiguity,
    /// hence the stored [`BoundInclusivity`] of the interval's start.
    OnStart(BoundInclusivity),
    /// Compared point is exactly on the end of the interval
    ///
    /// Since the point falls on a bound from the interval, it creates an ambiguity,
    /// hence the stored [`BoundInclusivity`] of the interval's end.
    OnEnd(BoundInclusivity),
    /// Compared point is within the interval
    Inside,
}

impl PointContainmentPosition {
    /// Strips information about ambiguities and conserves the variant
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::point_containment::{
    /// #     DisambiguatedPointContainmentPosition, PointContainmentPosition,
    /// # };
    /// assert_eq!(
    ///     PointContainmentPosition::OnStart(BoundInclusivity::Exclusive).strip(),
    ///     DisambiguatedPointContainmentPosition::OnStart,
    /// );
    /// ```
    #[must_use]
    pub fn strip(self) -> DisambiguatedPointContainmentPosition {
        match self {
            Self::OutsideBefore => DisambiguatedPointContainmentPosition::OutsideBefore,
            Self::OutsideAfter => DisambiguatedPointContainmentPosition::OutsideAfter,
            Self::Outside => DisambiguatedPointContainmentPosition::Outside,
            Self::OnStart(_) => DisambiguatedPointContainmentPosition::OnStart,
            Self::OnEnd(_) => DisambiguatedPointContainmentPosition::OnEnd,
            Self::Inside => DisambiguatedPointContainmentPosition::Inside,
        }
    }

    /// Disambiguates using a [`PointContainmentRuleSet`]
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::point_containment::{
    /// #     DisambiguatedPointContainmentPosition, PointContainmentPosition, PointContainmentRuleSet,
    /// # };
    /// assert_eq!(
    ///     PointContainmentPosition::OnStart(BoundInclusivity::Exclusive)
    ///         .disambiguate_using_rule_set(PointContainmentRuleSet::Strict),
    ///     DisambiguatedPointContainmentPosition::OutsideBefore,
    /// );
    /// assert_eq!(
    ///     PointContainmentPosition::OnStart(BoundInclusivity::Exclusive)
    ///         .disambiguate_using_rule_set(PointContainmentRuleSet::Lenient),
    ///     DisambiguatedPointContainmentPosition::OnStart,
    /// );
    /// ```
    #[must_use]
    pub fn disambiguate_using_rule_set(
        self,
        rule_set: PointContainmentRuleSet,
    ) -> DisambiguatedPointContainmentPosition {
        rule_set.disambiguate(self)
    }

    /// Disambiguates using the given closure
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::point_containment::{
    /// #     DisambiguatedPointContainmentPosition, PointContainmentPosition,
    /// # };
    /// // Weird disambiguation closure: only on start/end if exclusive
    /// let disambiguation_closure = |pos: PointContainmentPosition| -> DisambiguatedPointContainmentPosition {
    ///     type Pos = PointContainmentPosition;
    ///     type DisambiguatedPos = DisambiguatedPointContainmentPosition;
    ///     match pos {
    ///         Pos::OutsideBefore => DisambiguatedPos::OutsideBefore,
    ///         Pos::OutsideAfter => DisambiguatedPos::OutsideAfter,
    ///         Pos::Outside => DisambiguatedPos::Outside,
    ///         Pos::OnStart(BoundInclusivity::Inclusive) => DisambiguatedPos::OutsideBefore,
    ///         Pos::OnStart(BoundInclusivity::Exclusive) => DisambiguatedPos::OnStart,
    ///         Pos::OnEnd(BoundInclusivity::Inclusive) => DisambiguatedPos::OutsideAfter,
    ///         Pos::OnEnd(BoundInclusivity::Exclusive) => DisambiguatedPos::OnEnd,
    ///         Pos::Inside => DisambiguatedPos::Inside,
    ///     }
    /// };
    ///
    /// assert_eq!(
    ///     PointContainmentPosition::OnStart(BoundInclusivity::Inclusive)
    ///         .disambiguate_using(disambiguation_closure),
    ///     DisambiguatedPointContainmentPosition::OutsideBefore,
    /// );
    /// assert_eq!(
    ///     PointContainmentPosition::OnStart(BoundInclusivity::Exclusive)
    ///         .disambiguate_using(disambiguation_closure),
    ///     DisambiguatedPointContainmentPosition::OnStart,
    /// );
    /// ```
    #[must_use]
    pub fn disambiguate_using<F>(self, f: F) -> DisambiguatedPointContainmentPosition
    where
        F: FnOnce(PointContainmentPosition) -> DisambiguatedPointContainmentPosition,
    {
        (f)(self)
    }
}

/// Disambiguated [`PointContainmentPosition`]
///
/// Indicates where the point is situated compared to the interval without any ambiguity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum DisambiguatedPointContainmentPosition {
    /// See [`OutsideBefore`](PointContainmentPosition::OutsideBefore)
    OutsideBefore,
    /// See [`OutsideAfter`](PointContainmentPosition::OutsideAfter)
    OutsideAfter,
    /// See [`Outside`](PointContainmentPosition::Outside)
    Outside,
    /// See [`OnStart`](PointContainmentPosition::OnStart)
    OnStart,
    /// See [`OnEnd`](PointContainmentPosition::OnEnd)
    OnEnd,
    /// See [`Inside`](PointContainmentPosition::Inside)
    Inside,
}

/// Rule sets for disambiguating a [`PointContainmentPosition`]
///
/// See [`contains_point`](CanPositionPointContainment::contains_point) for more.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum PointContainmentRuleSet {
    /// Strict rule set
    ///
    /// Mathematical interpretation of bounds, so the point needs to fall on an inclusive bound in order to be counted
    /// as contained.
    #[default]
    Strict,
    /// Lenient rule set
    ///
    /// If the point falls on a bound, it counts as contained, regardless of the [`BoundInclusivity`].
    Lenient,
}

impl PointContainmentRuleSet {
    /// Disambiguates a [`PointContainmentPosition`] according to the rule set
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    ///
    /// Preferably use [`PointContainmentPosition::disambiguate_using_rule_set`] instead.
    ///
    /// # Examples
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::point_containment::{
    /// #     DisambiguatedPointContainmentPosition, PointContainmentPosition, PointContainmentRuleSet,
    /// # };
    /// assert_eq!(
    ///     PointContainmentRuleSet::Strict
    ///         .disambiguate(PointContainmentPosition::OnStart(BoundInclusivity::Exclusive)),
    ///     DisambiguatedPointContainmentPosition::OutsideBefore,
    /// );
    /// assert_eq!(
    ///     PointContainmentRuleSet::Lenient
    ///         .disambiguate(PointContainmentPosition::OnStart(BoundInclusivity::Exclusive)),
    ///     DisambiguatedPointContainmentPosition::OnStart,
    /// );
    /// ```
    #[must_use]
    pub fn disambiguate(
        &self,
        containment_position: PointContainmentPosition,
    ) -> DisambiguatedPointContainmentPosition {
        match self {
            Self::Strict => strict_containment_rule_set_disambiguation(containment_position),
            Self::Lenient => lenient_containment_rule_set_disambiguation(containment_position),
        }
    }
}

/// Disambiguates a [`PointContainmentPosition`] using [the strict rule set](PointContainmentRuleSet::Strict)
///
/// See [module documentation](crate::intervals::ops::point_containment) for more information.
#[must_use]
pub fn strict_containment_rule_set_disambiguation(
    containment_position: PointContainmentPosition,
) -> DisambiguatedPointContainmentPosition {
    match containment_position {
        PointContainmentPosition::OutsideBefore | PointContainmentPosition::OnStart(BoundInclusivity::Exclusive) => {
            DisambiguatedPointContainmentPosition::OutsideBefore
        },
        PointContainmentPosition::OutsideAfter | PointContainmentPosition::OnEnd(BoundInclusivity::Exclusive) => {
            DisambiguatedPointContainmentPosition::OutsideAfter
        },
        PointContainmentPosition::Outside => DisambiguatedPointContainmentPosition::Outside,
        PointContainmentPosition::OnStart(BoundInclusivity::Inclusive) => {
            DisambiguatedPointContainmentPosition::OnStart
        },
        PointContainmentPosition::OnEnd(BoundInclusivity::Inclusive) => DisambiguatedPointContainmentPosition::OnEnd,
        PointContainmentPosition::Inside => DisambiguatedPointContainmentPosition::Inside,
    }
}

/// Disambiguates a [`PointContainmentPosition`] using [the lenient rule set](PointContainmentRuleSet::Lenient)
///
/// See [module documentation](crate::intervals::ops::point_containment) for more information.
#[must_use]
pub fn lenient_containment_rule_set_disambiguation(
    containment_position: PointContainmentPosition,
) -> DisambiguatedPointContainmentPosition {
    match containment_position {
        PointContainmentPosition::OutsideBefore => DisambiguatedPointContainmentPosition::OutsideBefore,
        PointContainmentPosition::OutsideAfter => DisambiguatedPointContainmentPosition::OutsideAfter,
        PointContainmentPosition::Outside => DisambiguatedPointContainmentPosition::Outside,
        PointContainmentPosition::OnStart(_) => DisambiguatedPointContainmentPosition::OnStart,
        PointContainmentPosition::OnEnd(_) => DisambiguatedPointContainmentPosition::OnEnd,
        PointContainmentPosition::Inside => DisambiguatedPointContainmentPosition::Inside,
    }
}

/// Point containment rules used as the reference for predefined decisions
pub const DEFAULT_POINT_CONTAINMENT_RULES: [PointContainmentRule; 1] = [PointContainmentRule::AllowOnBounds];

/// Rules for determining what counts as containment
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(Arbitrary))]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum PointContainmentRule {
    /// Counts points that are on the interval's start
    AllowOnStart,
    /// Counts points that are on the interval's end
    AllowOnEnd,
    /// Counts points that are on either ends of an interval
    AllowOnBounds,
    /// Doesn't count points that are on the interval's start
    DenyOnStart,
    /// Doesn't count points that are on the interval's end
    DenyOnEnd,
    /// Doesn't count points that are on either ends of an interval
    DenyOnBounds,
}

impl PointContainmentRule {
    /// Returns the next state of the running containment decision
    ///
    /// This method takes the running containment decision and the [`DisambiguatedPointContainmentPosition`]
    /// and returns the next state of the running containment decision.
    #[must_use]
    pub fn counts_as_contained(&self, running: bool, disambiguated_pos: DisambiguatedPointContainmentPosition) -> bool {
        match self {
            Self::AllowOnStart => allow_on_start_containment_rule_counts_as_contained(running, disambiguated_pos),
            Self::AllowOnEnd => allow_on_end_containment_rule_counts_as_contained(running, disambiguated_pos),
            Self::AllowOnBounds => allow_on_bounds_containment_rule_counts_as_contained(running, disambiguated_pos),
            Self::DenyOnStart => deny_on_start_containment_rule_counts_as_contained(running, disambiguated_pos),
            Self::DenyOnEnd => deny_on_end_containment_rule_counts_as_contained(running, disambiguated_pos),
            Self::DenyOnBounds => deny_on_bounds_containment_rule_counts_as_contained(running, disambiguated_pos),
        }
    }
}

/// Checks all the given rules and returns the final boolean regarding containment
///
/// Iterates over the given rules and [fold](Iterator::fold) them with [`PointContainmentRule::counts_as_contained`]
/// in order to get the final boolean regarding whether the point is considered contained by the interval.
///
/// This method also contains the common logic of considering
/// the [`Inside`](DisambiguatedPointContainmentPosition::Inside) [`DisambiguatedPointContainmentPosition`]
/// as containment of the point.
#[must_use]
pub fn check_point_containment_rules<'a, RI>(
    disambiguated_pos: DisambiguatedPointContainmentPosition,
    rules: RI,
) -> bool
where
    RI: IntoIterator<Item = &'a PointContainmentRule>,
{
    let common = matches!(disambiguated_pos, DisambiguatedPointContainmentPosition::Inside);

    rules.into_iter().fold(common, |is_contained, rule| {
        rule.counts_as_contained(is_contained, disambiguated_pos)
    })
}

/// Checks whether the given [`DisambiguatedPointContainmentPosition`] respects
/// the ['allow on start' rule](PointContainmentRule::AllowOnStart)
#[must_use]
pub fn allow_on_start_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedPointContainmentPosition,
) -> bool {
    running || matches!(disambiguated_pos, DisambiguatedPointContainmentPosition::OnStart)
}

/// Checks whether the given [`DisambiguatedPointContainmentPosition`] respects
/// the ['allow on end' rule](PointContainmentRule::AllowOnEnd)
#[must_use]
pub fn allow_on_end_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedPointContainmentPosition,
) -> bool {
    running || matches!(disambiguated_pos, DisambiguatedPointContainmentPosition::OnEnd)
}

/// Checks whether the given [`DisambiguatedPointContainmentPosition`] respects
/// the ['allow on bounds' rule](PointContainmentRule::AllowOnBounds)
#[must_use]
pub fn allow_on_bounds_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedPointContainmentPosition,
) -> bool {
    running
        || matches!(
            disambiguated_pos,
            DisambiguatedPointContainmentPosition::OnStart | DisambiguatedPointContainmentPosition::OnEnd
        )
}

/// Checks whether the given [`DisambiguatedPointContainmentPosition`] respects
/// the ['deny on start' rule](PointContainmentRule::DenyOnStart)
#[must_use]
pub fn deny_on_start_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedPointContainmentPosition,
) -> bool {
    running && !matches!(disambiguated_pos, DisambiguatedPointContainmentPosition::OnStart)
}

/// Checks whether the given [`DisambiguatedPointContainmentPosition`] respects
/// the ['deny on end' rule](PointContainmentRule::DenyOnEnd)
#[must_use]
pub fn deny_on_end_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedPointContainmentPosition,
) -> bool {
    running && !matches!(disambiguated_pos, DisambiguatedPointContainmentPosition::OnEnd)
}

/// Checks whether the given [`DisambiguatedPointContainmentPosition`] respects
/// the ['deny on bounds' rule](PointContainmentRule::DenyOnBounds)
#[must_use]
pub fn deny_on_bounds_containment_rule_counts_as_contained(
    running: bool,
    disambiguated_pos: DisambiguatedPointContainmentPosition,
) -> bool {
    running
        && !matches!(
            disambiguated_pos,
            DisambiguatedPointContainmentPosition::OnStart | DisambiguatedPointContainmentPosition::OnEnd,
        )
}

/// Capacity to position a point in an interval
///
/// The generic type parameter `P` corresponds to the positionable type.
///
/// # Examples
///
/// ## Fetching the disambiguated position of a point
///
/// ```
/// # use chrono::{DateTime, Utc};
/// # use periodical::intervals::absolute::{
/// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
/// # };
/// # use periodical::intervals::ops::point_containment::{
/// #     CanPositionPointContainment, DisambiguatedPointContainmentPosition, PointContainmentRuleSet,
/// # };
/// let interval = AbsoluteBounds::new(
///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
/// );
///
/// let point = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
///
/// assert_eq!(
///     interval.disambiguated_point_containment_position(point, PointContainmentRuleSet::Strict),
///     Ok(DisambiguatedPointContainmentPosition::OnStart),
/// );
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
///
/// ## Checking if a point is contained in an interval
///
/// ```
/// # use chrono::{DateTime, Utc};
/// # use periodical::intervals::absolute::{
/// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
/// # };
/// # use periodical::intervals::ops::point_containment::{
/// #     CanPositionPointContainment, DisambiguatedPointContainmentPosition, PointContainmentRuleSet,
/// # };
/// let interval = AbsoluteBounds::new(
///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
///     )),
/// );
///
/// let point = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
///
/// assert!(interval.simple_contains_point(point));
/// # Ok::<(), chrono::format::ParseError>(())
/// ```
pub trait CanPositionPointContainment<P> {
    /// Error type if the point containment positioning failed
    type Error;

    /// Returns the [`PointContainmentPosition`] of the given point
    ///
    /// # Bound inclusivity
    ///
    /// When checking the containment position, the interval's bound inclusivities are considered as inclusive.
    /// Then, on cases where the result could be ambiguous, we store the inclusivity of the bound inside
    /// the [`PointContainmentPosition`] variant.
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionPointContainment::Error).
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::point_containment::{
    /// #     CanPositionPointContainment, PointContainmentPosition,
    /// # };
    /// let interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///         BoundInclusivity::Exclusive,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// let point = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// assert_eq!(
    ///     interval.point_containment_position(point),
    ///     Ok(PointContainmentPosition::OnStart(BoundInclusivity::Exclusive)),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    fn point_containment_position(&self, positionable: P) -> Result<PointContainmentPosition, Self::Error>;

    /// Returns the [`DisambiguatedPointContainmentPosition`] of the given point
    /// using the given [rule set](PointContainmentRuleSet)
    ///
    /// See [`CanPositionPointContainment::point_containment_position`] for more details about containment position.
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionPointContainment::Error).
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::ops::point_containment::{
    /// #     CanPositionPointContainment, DisambiguatedPointContainmentPosition, PointContainmentRuleSet,
    /// # };
    /// let interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// let point = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// assert_eq!(
    ///     interval.disambiguated_point_containment_position(point, PointContainmentRuleSet::Strict),
    ///     Ok(DisambiguatedPointContainmentPosition::OnStart),
    /// );
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    fn disambiguated_point_containment_position(
        &self,
        positionable: P,
        rule_set: PointContainmentRuleSet,
    ) -> Result<DisambiguatedPointContainmentPosition, Self::Error> {
        self.point_containment_position(positionable)
            .map(|containment_position| rule_set.disambiguate(containment_position))
    }

    /// Returns whether the given point is contained in the interval using predetermined rules
    ///
    /// Uses the [default rule set](PointContainmentRuleSet::default)
    /// with [default rules](DEFAULT_POINT_CONTAINMENT_RULES).
    ///
    /// The rule set has been chosen because they are the closest to how we mathematically
    /// and humanly interpret containment.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::ops::point_containment::CanPositionPointContainment;
    /// let interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// let point = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// assert!(interval.simple_contains_point(point));
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    ///
    /// # See also
    ///
    /// If you are looking to choose the rule set and the rules,
    /// see [`contains_point`](CanPositionPointContainment::contains_point).
    ///
    /// If you want even more granular control,
    /// see [`contains_point_using_disambiguated`](CanPositionPointContainment::contains_point_using_disambiguated).
    #[must_use]
    fn simple_contains_point(&self, positionable: P) -> bool {
        self.contains_point(
            positionable,
            PointContainmentRuleSet::default(),
            &DEFAULT_POINT_CONTAINMENT_RULES,
        )
    }

    /// Returns whether the given time is contained in the interval
    /// using the given [containment rules](PointContainmentRule)
    ///
    /// Uses [`disambiguated_point_containment_position`] under the hood.
    ///
    /// If this aforementioned method returns an [`Err`], then this method returns `false`.
    /// If it returns [`Ok`], then the [`PointContainmentRule`]s are checked.
    ///
    /// This method returns `true` only if all provided [`PointContainmentRule`]s are respected.
    /// This part of the process uses [`PointContainmentRule::counts_as_contained`].
    ///
    /// [`disambiguated_point_containment_position`]: CanPositionPointContainment::disambiguated_point_containment_position
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::ops::point_containment::{
    /// #     CanPositionPointContainment, PointContainmentRule, PointContainmentRuleSet,
    /// # };
    /// let interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// let point = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// assert!(interval.contains_point(
    ///     point,
    ///     PointContainmentRuleSet::Strict,
    ///     &[PointContainmentRule::AllowOnBounds],
    /// ));
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    ///
    /// # See also
    ///
    /// If you are looking for the simplest way of checking for point containment,
    /// see [`simple_contains_point`](CanPositionPointContainment::simple_contains_point).
    ///
    /// If you are looking for more control over what counts as contained,
    /// see [`contains_point_using_disambiguated`](CanPositionPointContainment::contains_point_using_disambiguated).
    ///
    /// If you want even more granular control over what counts as contained,
    /// see [`contains_point_using`](CanPositionPointContainment::contains_point_using).
    #[must_use]
    fn contains_point<'a, RI>(&self, positionable: P, rule_set: PointContainmentRuleSet, rules: RI) -> bool
    where
        RI: IntoIterator<Item = &'a PointContainmentRule>,
    {
        self.disambiguated_point_containment_position(positionable, rule_set)
            .map(|disambiguated_containment_position| {
                check_point_containment_rules(disambiguated_containment_position, rules)
            })
            .unwrap_or(false)
    }

    /// Returns whether the given point is contained in the interval using the given closure
    ///
    /// Uses [`point_containment_position`](CanPositionPointContainment::point_containment_position) under the hood.
    ///
    /// If this aforementioned method returns an [`Err`], then this method returns `false`.
    /// If it returns [`Ok`], then the provided closure is in charge of determining
    /// whether the [`PointContainmentPosition`] given by
    /// [`point_containment_position`](CanPositionPointContainment::point_containment_position) counts as
    /// the passed point being contained in the interval.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::point_containment::{CanPositionPointContainment, PointContainmentPosition};
    /// let interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// let point = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let containment_closure = |point_pos: PointContainmentPosition| -> bool {
    ///     matches!(
    ///         point_pos,
    ///         PointContainmentPosition::OnStart(BoundInclusivity::Exclusive)
    ///         | PointContainmentPosition::OnEnd(BoundInclusivity::Exclusive)
    ///         | PointContainmentPosition::Inside,
    ///     )
    /// };
    ///
    /// assert!(!interval.contains_point_using(point, containment_closure));
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    ///
    /// # See also
    ///
    /// If you are looking for control over what's considered as contained but still want
    /// predetermined [`DisambiguatedPointContainmentPosition`]s,
    /// see [`contains_point_using_disambiguated`](CanPositionPointContainment::contains_point_using_disambiguated).
    ///
    /// If you are looking for predetermined decisions on what's considered as contained,
    /// see [`contains_point`](CanPositionPointContainment::contains_point).
    #[must_use]
    fn contains_point_using<F>(&self, positionable: P, f: F) -> bool
    where
        F: FnOnce(PointContainmentPosition) -> bool,
    {
        self.point_containment_position(positionable).map(f).unwrap_or(false)
    }

    /// Returns whether the given point is contained in the interval using the given closure
    /// with a disambiguated position
    ///
    /// Uses [`disambiguated_point_containment_position`] under the hood.
    ///
    /// If this aforementioned method returns an [`Err`], then this method returns `false`.
    /// If it returns [`Ok`], then the provided function is in charge of determining
    /// whether the [`DisambiguatedPointContainmentPosition`] given by [`disambiguated_point_containment_position`]
    /// counts as contained or not.
    ///
    /// [`disambiguated_point_containment_position`]: CanPositionPointContainment::disambiguated_point_containment_position
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::{DateTime, Utc};
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::meta::BoundInclusivity;
    /// # use periodical::intervals::ops::point_containment::{
    /// #     CanPositionPointContainment, DisambiguatedPointContainmentPosition, PointContainmentRuleSet,
    /// # };
    /// let interval = AbsoluteBounds::new(
    ///     AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    ///     AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
    ///         "2025-01-01 10:00:00Z".parse::<DateTime<Utc>>()?,
    ///     )),
    /// );
    ///
    /// let point = "2025-01-01 08:00:00Z".parse::<DateTime<Utc>>()?;
    ///
    /// let containment_closure = |point_pos: DisambiguatedPointContainmentPosition| -> bool {
    ///     matches!(point_pos, DisambiguatedPointContainmentPosition::Inside)
    /// };
    ///
    /// assert!(!interval.contains_point_using_disambiguated(
    ///     point,
    ///     PointContainmentRuleSet::Strict,
    ///     containment_closure,
    /// ));
    /// # Ok::<(), chrono::format::ParseError>(())
    /// ```
    ///
    /// # See also
    ///
    /// If you are looking for more granular control over what's considered as contained,
    /// see [`contains_point_using`](CanPositionPointContainment::contains_point_using).
    ///
    /// If you are looking for predetermined decisions on what's considered as contained,
    /// see [`simple_contains_point`](CanPositionPointContainment::simple_contains_point).
    #[must_use]
    fn contains_point_using_disambiguated<F>(&self, positionable: P, rule_set: PointContainmentRuleSet, f: F) -> bool
    where
        F: FnOnce(DisambiguatedPointContainmentPosition) -> bool,
    {
        self.disambiguated_point_containment_position(positionable, rule_set)
            .map(f)
            .unwrap_or(false)
    }
}

impl<P> CanPositionPointContainment<P> for AbsoluteBounds
where
    P: Into<DateTime<Utc>>,
{
    type Error = Infallible;

    fn point_containment_position(&self, positionable: P) -> Result<PointContainmentPosition, Self::Error> {
        Ok(point_containment_position_abs_bounds(self, positionable.into()))
    }
}

impl<P> CanPositionPointContainment<P> for EmptiableAbsoluteBounds
where
    P: Into<DateTime<Utc>>,
{
    type Error = Infallible;

    fn point_containment_position(&self, positionable: P) -> Result<PointContainmentPosition, Self::Error> {
        let EmptiableAbsoluteBounds::Bound(bounds) = self else {
            return Ok(PointContainmentPosition::Outside);
        };

        Ok(point_containment_position_abs_bounds(bounds, positionable.into()))
    }
}

impl<P> CanPositionPointContainment<P> for AbsoluteInterval
where
    P: Into<DateTime<Utc>>,
{
    type Error = Infallible;

    fn point_containment_position(&self, positionable: P) -> Result<PointContainmentPosition, Self::Error> {
        let EmptiableAbsoluteBounds::Bound(bounds) = self.emptiable_abs_bounds() else {
            return Ok(PointContainmentPosition::Outside);
        };

        Ok(point_containment_position_abs_bounds(&bounds, positionable.into()))
    }
}

impl<P> CanPositionPointContainment<P> for BoundedAbsoluteInterval
where
    P: Into<DateTime<Utc>>,
{
    type Error = Infallible;

    fn point_containment_position(&self, positionable: P) -> Result<PointContainmentPosition, Self::Error> {
        Ok(point_containment_position_abs_bounds(
            &self.abs_bounds(),
            positionable.into(),
        ))
    }
}

impl<P> CanPositionPointContainment<P> for HalfBoundedAbsoluteInterval
where
    P: Into<DateTime<Utc>>,
{
    type Error = Infallible;

    fn point_containment_position(&self, positionable: P) -> Result<PointContainmentPosition, Self::Error> {
        Ok(point_containment_position_abs_bounds(
            &self.abs_bounds(),
            positionable.into(),
        ))
    }
}

impl<P> CanPositionPointContainment<P> for RelativeBounds
where
    P: Into<Duration>,
{
    type Error = Infallible;

    fn point_containment_position(&self, positionable: P) -> Result<PointContainmentPosition, Self::Error> {
        Ok(point_containment_position_rel_bounds(self, positionable.into()))
    }
}

impl<P> CanPositionPointContainment<P> for EmptiableRelativeBounds
where
    P: Into<Duration>,
{
    type Error = Infallible;

    fn point_containment_position(&self, positionable: P) -> Result<PointContainmentPosition, Self::Error> {
        let EmptiableRelativeBounds::Bound(bounds) = self else {
            return Ok(PointContainmentPosition::Outside);
        };

        Ok(point_containment_position_rel_bounds(bounds, positionable.into()))
    }
}

impl<P> CanPositionPointContainment<P> for RelativeInterval
where
    P: Into<Duration>,
{
    type Error = Infallible;

    fn point_containment_position(&self, positionable: P) -> Result<PointContainmentPosition, Self::Error> {
        let EmptiableRelativeBounds::Bound(bounds) = self.emptiable_rel_bounds() else {
            return Ok(PointContainmentPosition::Outside);
        };

        Ok(point_containment_position_rel_bounds(&bounds, positionable.into()))
    }
}

impl<P> CanPositionPointContainment<P> for BoundedRelativeInterval
where
    P: Into<Duration>,
{
    type Error = Infallible;

    fn point_containment_position(&self, positionable: P) -> Result<PointContainmentPosition, Self::Error> {
        Ok(point_containment_position_rel_bounds(
            &self.rel_bounds(),
            positionable.into(),
        ))
    }
}

impl<P> CanPositionPointContainment<P> for HalfBoundedRelativeInterval
where
    P: Into<Duration>,
{
    type Error = Infallible;

    fn point_containment_position(&self, positionable: P) -> Result<PointContainmentPosition, Self::Error> {
        Ok(point_containment_position_rel_bounds(
            &self.rel_bounds(),
            positionable.into(),
        ))
    }
}

// TODO: Find a way to implement these for P: Into<DateTime<Utc>> and P: Into<chrono::Duration>
impl CanPositionPointContainment<DateTime<Utc>> for UnboundedInterval {
    type Error = Infallible;

    fn point_containment_position(
        &self,
        _positionable: DateTime<Utc>,
    ) -> Result<PointContainmentPosition, Self::Error> {
        Ok(PointContainmentPosition::Inside)
    }
}

impl CanPositionPointContainment<Duration> for UnboundedInterval {
    type Error = Infallible;

    fn point_containment_position(&self, _positionable: Duration) -> Result<PointContainmentPosition, Self::Error> {
        Ok(PointContainmentPosition::Inside)
    }
}

// TODO: Find a way to implement these for P: Into<DateTime<Utc>> and P: Into<chrono::Duration>
impl CanPositionPointContainment<DateTime<Utc>> for EmptyInterval {
    type Error = Infallible;

    fn point_containment_position(
        &self,
        _positionable: DateTime<Utc>,
    ) -> Result<PointContainmentPosition, Self::Error> {
        Ok(PointContainmentPosition::Outside)
    }
}

impl CanPositionPointContainment<Duration> for EmptyInterval {
    type Error = Infallible;

    fn point_containment_position(&self, _positionable: Duration) -> Result<PointContainmentPosition, Self::Error> {
        Ok(PointContainmentPosition::Outside)
    }
}

/// Returns the [`PointContainmentPosition`] of the given time within the given [`AbsoluteBounds`]
#[must_use]
pub fn point_containment_position_abs_bounds(bounds: &AbsoluteBounds, time: DateTime<Utc>) -> PointContainmentPosition {
    type StartB = AbsoluteStartBound;
    type EndB = AbsoluteEndBound;
    type ContPos = PointContainmentPosition;

    match (bounds.abs_start(), bounds.abs_end()) {
        (StartB::InfinitePast, EndB::InfiniteFuture) => ContPos::Inside,
        (StartB::InfinitePast, EndB::Finite(finite_bound)) => match time.cmp(&finite_bound.time()) {
            Ordering::Less => ContPos::Inside,
            Ordering::Equal => ContPos::OnEnd(finite_bound.inclusivity()),
            Ordering::Greater => ContPos::OutsideAfter,
        },
        (StartB::Finite(finite_bound), EndB::InfiniteFuture) => match time.cmp(&finite_bound.time()) {
            Ordering::Less => ContPos::OutsideBefore,
            Ordering::Equal => ContPos::OnStart(finite_bound.inclusivity()),
            Ordering::Greater => ContPos::Inside,
        },
        (StartB::Finite(start_bound), EndB::Finite(end_bound)) => {
            match (time.cmp(&start_bound.time()), time.cmp(&end_bound.time())) {
                (Ordering::Less, _) => ContPos::OutsideBefore,
                (Ordering::Equal, _) => ContPos::OnStart(start_bound.inclusivity()),
                (_, Ordering::Less) => ContPos::Inside,
                (_, Ordering::Equal) => ContPos::OnEnd(end_bound.inclusivity()),
                (_, Ordering::Greater) => ContPos::OutsideAfter,
            }
        },
    }
}

/// Returns the [`PointContainmentPosition`] of the given offset within the given [`RelativeBounds`]
#[must_use]
pub fn point_containment_position_rel_bounds(bounds: &RelativeBounds, offset: Duration) -> PointContainmentPosition {
    type StartB = RelativeStartBound;
    type EndB = RelativeEndBound;
    type ContPos = PointContainmentPosition;

    match (bounds.rel_start(), bounds.rel_end()) {
        (StartB::InfinitePast, EndB::InfiniteFuture) => ContPos::Inside,
        (StartB::InfinitePast, EndB::Finite(finite_bound)) => match offset.cmp(&finite_bound.offset()) {
            Ordering::Less => ContPos::Inside,
            Ordering::Equal => ContPos::OnEnd(finite_bound.inclusivity()),
            Ordering::Greater => ContPos::OutsideAfter,
        },
        (StartB::Finite(finite_bound), EndB::InfiniteFuture) => match offset.cmp(&finite_bound.offset()) {
            Ordering::Less => ContPos::OutsideBefore,
            Ordering::Equal => ContPos::OnStart(finite_bound.inclusivity()),
            Ordering::Greater => ContPos::Inside,
        },
        (StartB::Finite(start_bound), EndB::Finite(end_bound)) => {
            match (offset.cmp(&start_bound.offset()), offset.cmp(&end_bound.offset())) {
                (Ordering::Less, _) => ContPos::OutsideBefore,
                (Ordering::Equal, _) => ContPos::OnStart(start_bound.inclusivity()),
                (_, Ordering::Less) => ContPos::Inside,
                (_, Ordering::Equal) => ContPos::OnEnd(end_bound.inclusivity()),
                (_, Ordering::Greater) => ContPos::OutsideAfter,
            }
        },
    }
}

//! Interval time containment positioning

use std::cmp::Ordering;
use std::convert::Infallible;

use chrono::{DateTime, Duration, Utc};

use super::prelude::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteStartBound, EmptiableAbsoluteBounds, HalfOpenAbsoluteInterval,
    HasAbsoluteBounds, HasEmptiableAbsoluteBounds,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{
    EmptiableRelativeBounds, HalfOpenRelativeInterval, RelativeBounds, RelativeEndBound, RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, OpenInterval};
use crate::intervals::{AbsoluteInterval, ClosedAbsoluteInterval, ClosedRelativeInterval, RelativeInterval};

/// Where the given time was found relative to a time interval
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TimeContainmentPosition {
    /// The given time was found before the time interval's beginning
    OutsideBefore,
    /// The given time was found after the time interval's end
    OutsideAfter,
    /// The given time was found outside the time interval (result only possible when dealing with empty intervals)
    Outside,
    /// The given time was found exactly on the start of the time interval
    ///
    /// The contained bound inclusivity indicates the bound inclusivity of the start bound.
    ///
    /// See [`Interval::containment_position`] for more details.
    OnStart(BoundInclusivity),
    /// The given time was found exactly on the end of the time interval
    ///
    /// The contained bound inclusivity indicates the bound inclusivity of the end bound.
    ///
    /// See [`Interval::containment_position`] for more details.
    OnEnd(BoundInclusivity),
    /// The given time was found within the time interval
    Inside,
}

impl TimeContainmentPosition {
    /// Discards the information about bound inclusivity but conserves the variant
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn disambiguate(self) -> DisambiguatedTimeContainmentPosition {
        match self {
            Self::OutsideBefore => DisambiguatedTimeContainmentPosition::OutsideBefore,
            Self::OutsideAfter => DisambiguatedTimeContainmentPosition::OutsideAfter,
            Self::Outside => DisambiguatedTimeContainmentPosition::Outside,
            Self::OnStart(_) => DisambiguatedTimeContainmentPosition::OnStart,
            Self::OnEnd(_) => DisambiguatedTimeContainmentPosition::OnEnd,
            Self::Inside => DisambiguatedTimeContainmentPosition::Inside,
        }
    }

    /// Uses a rule set to transform the containment position into a disambiguated one.
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn disambiguate_using_rule_set(self, rule_set: TimeContainmentRuleSet) -> DisambiguatedTimeContainmentPosition {
        rule_set.disambiguate(self)
    }
}

/// Same as [`TimeContainmentPosition`] but without information about bound inclusivity
///
/// Used for methods that resolve ambiguities caused by bound inclusivity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DisambiguatedTimeContainmentPosition {
    /// See [`OutsideBefore`](TimeContainmentPosition::OutsideBefore)
    OutsideBefore,
    /// See [`OutsideAfter`](TimeContainmentPosition::OutsideAfter)
    OutsideAfter,
    /// See [`Outside`](TimeContainmentPosition::Outside)
    Outside,
    /// See [`OnStart`](TimeContainmentPosition::OnStart)
    OnStart,
    /// See [`OnEnd`](TimeContainmentPosition::OnEnd)
    OnEnd,
    /// See [`Inside`](TimeContainmentPosition::Inside)
    Inside,
}

/// Different rule sets for determining whether different [`TimeContainmentPosition`]s are considered as containing or not.
///
/// See [`contains`](CanPositionTimeContainment::contains) for more.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum TimeContainmentRuleSet {
    /// Strict rule set
    ///
    /// Mathematical interpretation of bounds, so the time needs to fall on an inclusive bound in order to be counted
    /// as contained.
    #[default]
    Strict,
    /// Lenient rule set
    ///
    /// If the time falls on an exclusive bound, it is still counted as contained.
    Lenient,
}

impl TimeContainmentRuleSet {
    /// Disambiguates a containment position according to the rule set
    ///
    /// **Careful!** This method discards data about bound inclusivity and cannot be recovered after conversion.
    #[must_use]
    pub fn disambiguate(&self, containment_position: TimeContainmentPosition) -> DisambiguatedTimeContainmentPosition {
        match self {
            Self::Strict => strict_containment_rule_set_disambiguation(containment_position),
            Self::Lenient => lenient_containment_rule_set_disambiguation(containment_position),
        }
    }
}

/// Disambiguates a [`TimeContainmentPosition`] using [the strict rule set](TimeContainmentRuleSet::Strict)
#[must_use]
pub fn strict_containment_rule_set_disambiguation(
    containment_position: TimeContainmentPosition,
) -> DisambiguatedTimeContainmentPosition {
    match containment_position {
        TimeContainmentPosition::OutsideBefore | TimeContainmentPosition::OnStart(BoundInclusivity::Exclusive) => {
            DisambiguatedTimeContainmentPosition::OutsideBefore
        },
        TimeContainmentPosition::OutsideAfter | TimeContainmentPosition::OnEnd(BoundInclusivity::Exclusive) => {
            DisambiguatedTimeContainmentPosition::OutsideAfter
        },
        TimeContainmentPosition::Outside => DisambiguatedTimeContainmentPosition::Outside,
        TimeContainmentPosition::OnStart(BoundInclusivity::Inclusive) => DisambiguatedTimeContainmentPosition::OnStart,
        TimeContainmentPosition::OnEnd(BoundInclusivity::Inclusive) => DisambiguatedTimeContainmentPosition::OnEnd,
        TimeContainmentPosition::Inside => DisambiguatedTimeContainmentPosition::Inside,
    }
}

/// Disambiguates a [`TimeContainmentPosition`] using [the lenient rule set](TimeContainmentRuleSet::Lenient)
#[must_use]
pub fn lenient_containment_rule_set_disambiguation(
    containment_position: TimeContainmentPosition,
) -> DisambiguatedTimeContainmentPosition {
    match containment_position {
        TimeContainmentPosition::OutsideBefore => DisambiguatedTimeContainmentPosition::OutsideBefore,
        TimeContainmentPosition::OutsideAfter => DisambiguatedTimeContainmentPosition::OutsideAfter,
        TimeContainmentPosition::Outside => DisambiguatedTimeContainmentPosition::Outside,
        TimeContainmentPosition::OnStart(_) => DisambiguatedTimeContainmentPosition::OnStart,
        TimeContainmentPosition::OnEnd(_) => DisambiguatedTimeContainmentPosition::OnEnd,
        TimeContainmentPosition::Inside => DisambiguatedTimeContainmentPosition::Inside,
    }
}

/// Time containment rules used as the reference for the predefined decisions
pub const DEFAULT_TIME_CONTAINMENT_RULES: [TimeContainmentRule; 0] = [];

/// All rules for containment by converting a [`DisambiguatedTimeContainmentPosition`] into a [`bool`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TimeContainmentRule {
    /// Doesn't count as contained when the time is on the start of the interval
    DenyOnStart,
    /// Doesn't count as contained when the time is on the end of the interval
    DenyOnEnd,
    /// Doesn't count as contained when the time is on either end of the interval
    DenyOnBounds,
}

impl TimeContainmentRule {
    /// Returns whether the given [`SimpleContainmentPosition`] counts as contained
    #[must_use]
    pub fn counts_as_contained(&self, simple_containment_position: DisambiguatedTimeContainmentPosition) -> bool {
        match self {
            Self::DenyOnStart => deny_on_start_containment_rule_counts_as_contained(simple_containment_position),
            Self::DenyOnEnd => deny_on_end_containment_rule_counts_as_contained(simple_containment_position),
            Self::DenyOnBounds => deny_on_bounds_containment_rule_counts_as_contained(simple_containment_position),
        }
    }
}

/// Checks whether the given [`DisambiguatedTimeContainmentPosition`] respects [the 'deny on start' rule](TimeContainmentRule::DenyOnStart)
#[must_use]
pub fn deny_on_start_containment_rule_counts_as_contained(
    simple_containment_position: DisambiguatedTimeContainmentPosition,
) -> bool {
    !matches!(
        simple_containment_position,
        DisambiguatedTimeContainmentPosition::OutsideBefore
            | DisambiguatedTimeContainmentPosition::OutsideAfter
            | DisambiguatedTimeContainmentPosition::Outside
            | DisambiguatedTimeContainmentPosition::OnStart
    )
}

/// Checks whether the given [`DisambiguatedTimeContainmentPosition`] respects [the 'deny on end' rule](TimeContainmentRule::DenyOnEnd)
#[must_use]
pub fn deny_on_end_containment_rule_counts_as_contained(
    simple_containment_position: DisambiguatedTimeContainmentPosition,
) -> bool {
    !matches!(
        simple_containment_position,
        DisambiguatedTimeContainmentPosition::OutsideBefore
            | DisambiguatedTimeContainmentPosition::OutsideAfter
            | DisambiguatedTimeContainmentPosition::Outside
            | DisambiguatedTimeContainmentPosition::OnEnd
    )
}

/// Checks whether the given [`DisambiguatedTimeContainmentPosition`] respects [the 'deny on bounds' rule](TimeContainmentRule::DenyOnBounds)
#[must_use]
pub fn deny_on_bounds_containment_rule_counts_as_contained(
    simple_containment_position: DisambiguatedTimeContainmentPosition,
) -> bool {
    !matches!(
        simple_containment_position,
        DisambiguatedTimeContainmentPosition::OutsideBefore
            | DisambiguatedTimeContainmentPosition::OutsideAfter
            | DisambiguatedTimeContainmentPosition::Outside
            | DisambiguatedTimeContainmentPosition::OnStart
            | DisambiguatedTimeContainmentPosition::OnEnd
    )
}

/// Capacity to position where a given time is contained in an interval
///
/// The generic type parameter `P` corresponds to the positionable type
pub trait CanPositionTimeContainment<P> {
    /// Error type if the time containment positioning failed
    type Error;

    /// Returns the containment position of the given time
    ///
    /// # Bound inclusivity
    ///
    /// When checking the containment position, the reference interval's bound inclusivities are considered
    /// as inclusive. Then, on cases where the result could be ambiguous (e.g. if the time ends up on the reference
    /// interval's start but the inclusivity of this bound is exclusive, does it qualify
    /// as [`TimeContainmentPosition::OnStart`]?), we simply include the inclusivity of the concerned bound and let the
    /// receiver make the call on whether it counts or not.
    ///
    /// This way, we can guarantee maximum flexibility of this process.
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionTimeContainment::Error).
    fn time_containment_position(&self, positionable: P) -> Result<TimeContainmentPosition, Self::Error>;

    /// Returns the disambiguated containment position of the given time using a given [containment rule set](TimeContainmentRuleSet)
    ///
    /// See [`CanPositionTimeContainment::time_containment_position`] for more details about containment position.
    ///
    /// # Errors
    ///
    /// If this process is fallible in a given implementor,
    /// they can use the associated type [`Error`](CanPositionTimeContainment::Error).
    fn disambiguated_time_containment_position(
        &self,
        positionable: P,
        rule_set: TimeContainmentRuleSet,
    ) -> Result<DisambiguatedTimeContainmentPosition, Self::Error> {
        self.time_containment_position(positionable)
            .map(|containment_position| rule_set.disambiguate(containment_position))
    }

    /// Returns whether the given time is contained in the interval using predetermined rules
    ///
    /// Uses the [default rule set](TimeContainmentRuleSet::default) with default rules.
    ///
    /// The rule set has been chosen because they are the closest to how we mathematically
    /// and humanly interpret containment.
    ///
    /// # See also
    ///
    /// If you are looking to choose the rule set and the rules, see [`contains`](CanPositionTimeContainment::contains).
    ///
    /// If you want even more granular control, see [`contains_using_simple`](CanPositionTimeContainment::contains_using_simple).
    #[must_use]
    fn simple_contains(&self, positionable: P) -> bool {
        self.contains(
            positionable,
            TimeContainmentRuleSet::default(),
            &DEFAULT_TIME_CONTAINMENT_RULES,
        )
    }

    /// Returns whether the given time is contained in the interval using the given [containment rules](`TimeContainmentRule`)
    ///
    /// This method uses [`disambiguated_time_containment_position`](CanPositionTimeContainment::disambiguated_time_containment_position).
    /// If this aforementioned method returns an [`Err`], then this method returns false.
    ///
    /// If it returns [`Ok`], then the [`TimeContainmentRule`]s are checked. This method returns true only if all provided
    /// [`TimeContainmentRule`]s are respected (i.e. returned true when calling [`TimeContainmentRule::counts_as_contained`]).
    ///
    /// # See also
    ///
    /// If you are looking for the simplest way of checking for containment, see [`simple_contains`](CanPositionTimeContainment::simple_contains).
    ///
    /// If you are looking for more control over what counts as contained, see [`contains_using_simple`](CanPositionTimeContainment::contains_using_simple).
    ///
    /// If you want extremely granular control over what counts as contained, see [`contains_using`](CanPositionTimeContainment::contains_using).
    #[must_use]
    fn contains<'a, RI>(&self, positionable: P, rule_set: TimeContainmentRuleSet, rules: RI) -> bool
    where
        RI: IntoIterator<Item = &'a TimeContainmentRule>,
    {
        self.disambiguated_time_containment_position(positionable, rule_set)
            .map(|disambiguated_containment_position| {
                rules
                    .into_iter()
                    .all(|rule| rule.counts_as_contained(disambiguated_containment_position))
            })
            .unwrap_or(false)
    }

    /// Returns whether the given time is contained in the interval using a custom function
    ///
    /// This method uses [`time_containment_position`](CanPositionTimeContainment::time_containment_position).
    /// If this aforementioned method returns an [`Err`], then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`TimeContainmentPosition`]
    /// given by [`time_containment_position`](CanPositionTimeContainment::time_containment_position) counts as
    /// the passed time being contained in the interval.
    ///
    /// # See also
    ///
    /// If you are looking for control over what's considered as containment but still want
    /// predetermined [`DisambiguatedTimeContainmentPosition`]s, see [`contains_using_simple`](CanPositionTimeContainment::contains_using_simple).
    ///
    /// If you are looking for predetermined decisions on what's considered as contained, see [`contains`](CanPositionTimeContainment::contains).
    #[must_use]
    fn contains_using<F>(&self, positionable: P, f: F) -> bool
    where
        F: FnOnce(TimeContainmentPosition) -> bool,
    {
        self.time_containment_position(positionable).map(f).unwrap_or(false)
    }

    /// Returns whether the given time is contained in the interval using a custom function
    ///
    /// This method uses [`disambiguated_time_containment_position`](CanPositionTimeContainment::disambiguated_time_containment_position).
    /// If this aforementioned method returns an [`Err`], then this method returns false.
    ///
    /// If it returns [`Ok`], then the provided function is in charge of determining whether the [`DisambiguatedTimeContainmentPosition`]
    /// given by [`disambiguated_time_containment_position`](CanPositionTimeContainment::disambiguated_time_containment_position) counts as contained or not.
    ///
    /// # See also
    ///
    /// If you are looking for more granular control over what's considered as contained, see [`contains_using`](CanPositionTimeContainment::contains_using).
    ///
    /// If you are looking for predetermined decisions on what's considered as contained, see [`simple_contains`](CanPositionTimeContainment::simple_contains).
    #[must_use]
    fn contains_using_simple<F>(&self, positionable: P, rule_set: TimeContainmentRuleSet, f: F) -> bool
    where
        F: FnOnce(DisambiguatedTimeContainmentPosition) -> bool,
    {
        self.disambiguated_time_containment_position(positionable, rule_set)
            .map(f)
            .unwrap_or(false)
    }
}

impl<P> CanPositionTimeContainment<P> for AbsoluteBounds
where
    P: Into<DateTime<Utc>>,
{
    type Error = Infallible;

    fn time_containment_position(&self, positionable: P) -> Result<TimeContainmentPosition, Self::Error> {
        Ok(time_containment_position_abs_bounds(self, positionable.into()))
    }
}

impl<P> CanPositionTimeContainment<P> for EmptiableAbsoluteBounds
where
    P: Into<DateTime<Utc>>,
{
    type Error = Infallible;

    fn time_containment_position(&self, positionable: P) -> Result<TimeContainmentPosition, Self::Error> {
        let EmptiableAbsoluteBounds::Bound(bounds) = self else {
            return Ok(TimeContainmentPosition::Outside);
        };

        Ok(time_containment_position_abs_bounds(bounds, positionable.into()))
    }
}

impl<P> CanPositionTimeContainment<P> for AbsoluteInterval
where
    P: Into<DateTime<Utc>>,
{
    type Error = Infallible;

    fn time_containment_position(&self, positionable: P) -> Result<TimeContainmentPosition, Self::Error> {
        let EmptiableAbsoluteBounds::Bound(bounds) = self.emptiable_abs_bounds() else {
            return Ok(TimeContainmentPosition::Outside);
        };

        Ok(time_containment_position_abs_bounds(&bounds, positionable.into()))
    }
}

impl<P> CanPositionTimeContainment<P> for ClosedAbsoluteInterval
where
    P: Into<DateTime<Utc>>,
{
    type Error = Infallible;

    fn time_containment_position(&self, positionable: P) -> Result<TimeContainmentPosition, Self::Error> {
        Ok(time_containment_position_abs_bounds(
            &self.abs_bounds(),
            positionable.into(),
        ))
    }
}

impl<P> CanPositionTimeContainment<P> for HalfOpenAbsoluteInterval
where
    P: Into<DateTime<Utc>>,
{
    type Error = Infallible;

    fn time_containment_position(&self, positionable: P) -> Result<TimeContainmentPosition, Self::Error> {
        Ok(time_containment_position_abs_bounds(
            &self.abs_bounds(),
            positionable.into(),
        ))
    }
}

impl<P> CanPositionTimeContainment<P> for RelativeBounds
where
    P: Into<Duration>,
{
    type Error = Infallible;

    fn time_containment_position(&self, positionable: P) -> Result<TimeContainmentPosition, Self::Error> {
        Ok(time_containment_position_rel_bounds(self, positionable.into()))
    }
}

impl<P> CanPositionTimeContainment<P> for EmptiableRelativeBounds
where
    P: Into<Duration>,
{
    type Error = Infallible;

    fn time_containment_position(&self, positionable: P) -> Result<TimeContainmentPosition, Self::Error> {
        let EmptiableRelativeBounds::Bound(bounds) = self else {
            return Ok(TimeContainmentPosition::Outside);
        };

        Ok(time_containment_position_rel_bounds(bounds, positionable.into()))
    }
}

impl<P> CanPositionTimeContainment<P> for RelativeInterval
where
    P: Into<Duration>,
{
    type Error = Infallible;

    fn time_containment_position(&self, positionable: P) -> Result<TimeContainmentPosition, Self::Error> {
        let EmptiableRelativeBounds::Bound(bounds) = self.emptiable_rel_bounds() else {
            return Ok(TimeContainmentPosition::Outside);
        };

        Ok(time_containment_position_rel_bounds(&bounds, positionable.into()))
    }
}

impl<P> CanPositionTimeContainment<P> for ClosedRelativeInterval
where
    P: Into<Duration>,
{
    type Error = Infallible;

    fn time_containment_position(&self, positionable: P) -> Result<TimeContainmentPosition, Self::Error> {
        Ok(time_containment_position_rel_bounds(
            &self.rel_bounds(),
            positionable.into(),
        ))
    }
}

impl<P> CanPositionTimeContainment<P> for HalfOpenRelativeInterval
where
    P: Into<Duration>,
{
    type Error = Infallible;

    fn time_containment_position(&self, positionable: P) -> Result<TimeContainmentPosition, Self::Error> {
        Ok(time_containment_position_rel_bounds(
            &self.rel_bounds(),
            positionable.into(),
        ))
    }
}

// TODO: Find a way to implement these for P: Into<DateTime<Utc>> and P: Into<chrono::Duration>
impl CanPositionTimeContainment<DateTime<Utc>> for OpenInterval {
    type Error = Infallible;

    fn time_containment_position(&self, _positionable: DateTime<Utc>) -> Result<TimeContainmentPosition, Self::Error> {
        Ok(TimeContainmentPosition::Inside)
    }
}

impl CanPositionTimeContainment<Duration> for OpenInterval {
    type Error = Infallible;

    fn time_containment_position(&self, _positionable: Duration) -> Result<TimeContainmentPosition, Self::Error> {
        Ok(TimeContainmentPosition::Inside)
    }
}

// TODO: Find a way to implement these for P: Into<DateTime<Utc>> and P: Into<chrono::Duration>
impl CanPositionTimeContainment<DateTime<Utc>> for EmptyInterval {
    type Error = Infallible;

    fn time_containment_position(&self, _positionable: DateTime<Utc>) -> Result<TimeContainmentPosition, Self::Error> {
        Ok(TimeContainmentPosition::Outside)
    }
}

impl CanPositionTimeContainment<Duration> for EmptyInterval {
    type Error = Infallible;

    fn time_containment_position(&self, _positionable: Duration) -> Result<TimeContainmentPosition, Self::Error> {
        Ok(TimeContainmentPosition::Outside)
    }
}

/// Returns the [`TimeContainmentPosition`] of the given time within the given [`AbsoluteBounds`]
#[must_use]
pub fn time_containment_position_abs_bounds(bounds: &AbsoluteBounds, time: DateTime<Utc>) -> TimeContainmentPosition {
    type StartB = AbsoluteStartBound;
    type EndB = AbsoluteEndBound;
    type ContPos = TimeContainmentPosition;

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

/// Returns the [`TimeContainmentPosition`] of the given offset within the given [`RelativeBounds`]
#[must_use]
pub fn time_containment_position_rel_bounds(bounds: &RelativeBounds, offset: Duration) -> TimeContainmentPosition {
    type StartB = RelativeStartBound;
    type EndB = RelativeEndBound;
    type ContPos = TimeContainmentPosition;

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

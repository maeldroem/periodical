use std::cmp::Ordering;
use std::error::Error;
use std::time::Duration;

use jiff::Timestamp;

use super::emptiable_interval::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    HalfBoundedAbsoluteInterval,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::{
    Duration as IntervalDuration,
    Epsilon,
    HasDuration,
    HasOpenness,
    HasRelativity,
    IsEmpty,
    OpeningDirection,
    Openness,
    Relativity,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[test]
fn from_range() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        EmptiableAbsoluteInterval::from_range(start..),
        HalfBoundedAbsoluteInterval::new_from_time(start, OpeningDirection::ToFuture).to_emptiable_interval()
    );
    Ok(())
}

#[test]
fn bound() -> Result<(), Box<dyn Error>> {
    let interval =
        HalfBoundedAbsoluteInterval::new_from_time("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture);

    assert_eq!(
        interval.clone().to_emptiable_interval().bound(),
        Some(interval.to_interval())
    );
    assert_eq!(EmptiableAbsoluteInterval::Empty(EmptyInterval).bound(), None);
    Ok(())
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn bounded_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-03 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn bounded_bounded_start_equal_length_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-03 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn bounded_bounded_start_equal_length_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn bounded_bounded_start_equal_length_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn bounded_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn bounded_half_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn bounded_half_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn bounded_half_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture,
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn bounded_half_bounded_start_greater_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToPast
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn bounded_unbounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(&AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn bounded_empty() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(&EmptiableAbsoluteInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-03 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_less_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture,
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_less_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture,
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_equal_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToPast
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_greater_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToPast
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_empty() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(&EmptiableAbsoluteInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn unbounded_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                    ))
                    .to_emptiable()
                ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn unbounded_half_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        OpeningDirection::ToPast
                    ))
                    .to_emptiable()
                ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn unbounded_half_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        OpeningDirection::ToFuture
                    ))
                    .to_emptiable()
                ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(&AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Equal
        );
    }

    #[test]
    fn unbounded_empty() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(&EmptiableAbsoluteInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn empty_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsoluteInterval::Empty(EmptyInterval).ord_by_start_and_inv_length(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn empty_half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsoluteInterval::Empty(EmptyInterval).ord_by_start_and_inv_length(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn empty_unbounded() {
        assert_eq!(
            EmptiableAbsoluteInterval::Empty(EmptyInterval)
                .ord_by_start_and_inv_length(&AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Less
        );
    }

    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableAbsoluteInterval::Empty(EmptyInterval)
                .ord_by_start_and_inv_length(&EmptiableAbsoluteInterval::Empty(EmptyInterval)),
            Ordering::Equal
        );
    }
}

mod duration {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .duration(),
            IntervalDuration::Finite(Duration::from_hours(24), Epsilon::None)
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .duration(),
            IntervalDuration::Infinite
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable().duration(),
            IntervalDuration::Infinite
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableAbsoluteInterval::Empty(EmptyInterval).duration(),
            IntervalDuration::Finite(Duration::ZERO, Epsilon::None)
        );
    }
}

mod relativity {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .relativity(),
            Relativity::Absolute
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .relativity(),
            Relativity::Absolute
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .relativity(),
            Relativity::Any
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableAbsoluteInterval::Empty(EmptyInterval).relativity(),
            Relativity::Any
        );
    }
}

mod openness {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .openness(),
            Openness::Bounded
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .openness(),
            Openness::HalfBounded
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable().openness(),
            Openness::Unbounded
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableAbsoluteInterval::Empty(EmptyInterval).openness(),
            Openness::Empty
        );
    }
}

mod emptiable_abs_bound_pair {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .emptiable_abs_bound_pair(),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )
            .to_emptiable()
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .emptiable_abs_bound_pair(),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture
            )
            .to_emptiable()
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .emptiable_abs_bound_pair(),
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).to_emptiable()
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableAbsoluteInterval::Empty(EmptyInterval).emptiable_abs_bound_pair(),
            EmptiableAbsoluteBoundPair::Empty
        );
    }
}

mod partial_abs_start {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .partial_abs_start(),
            Some(AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .partial_abs_start(),
            Some(AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .partial_abs_start(),
            Some(AbsoluteStartBound::InfinitePast)
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .partial_abs_start(),
            Some(AbsoluteStartBound::InfinitePast)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableAbsoluteInterval::Empty(EmptyInterval).partial_abs_start(),
            None
        );
    }
}

mod partial_abs_end {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .partial_abs_end(),
            Some(AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .partial_abs_end(),
            Some(AbsoluteEndBound::InfiniteFuture)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .partial_abs_end(),
            Some(AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound())
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .partial_abs_end(),
            Some(AbsoluteEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(EmptiableAbsoluteInterval::Empty(EmptyInterval).partial_abs_end(), None);
    }
}

mod is_empty {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert!(
            !AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .is_empty()
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert!(
            !AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .is_empty()
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert!(!AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable().is_empty());
    }

    #[test]
    fn empty() {
        assert!(EmptiableAbsoluteInterval::Empty(EmptyInterval).is_empty());
    }
}

mod ord {
    use super::*;

    #[test]
    fn bounded_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-03 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn bounded_bounded_start_equal_length_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-03 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn bounded_bounded_start_equal_length_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn bounded_bounded_start_equal_length_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn bounded_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn bounded_half_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn bounded_half_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn bounded_half_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture,
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn bounded_half_bounded_start_greater_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToPast
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn bounded_unbounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(&AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn bounded_empty() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(&EmptiableAbsoluteInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-03 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_less_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture,
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_less_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture,
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_equal_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToPast
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_greater_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToPast
                ))
                .to_emptiable()
            ),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_empty() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(&EmptiableAbsoluteInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn unbounded_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn unbounded_half_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToPast
                ))
                .to_emptiable()
            ),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn unbounded_half_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .cmp(&AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Equal
        );
    }

    #[test]
    fn unbounded_empty() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .cmp(&EmptiableAbsoluteInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn empty_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsoluteInterval::Empty(EmptyInterval).cmp(
                &AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn empty_half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsoluteInterval::Empty(EmptyInterval).cmp(
                &AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                ))
                .to_emptiable()
            ),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn empty_unbounded() {
        assert_eq!(
            EmptiableAbsoluteInterval::Empty(EmptyInterval)
                .cmp(&AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Less
        );
    }

    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableAbsoluteInterval::Empty(EmptyInterval).cmp(&EmptiableAbsoluteInterval::Empty(EmptyInterval)),
            Ordering::Equal
        );
    }
}

#[test]
fn from_bounded_interval() -> Result<(), Box<dyn Error>> {
    let bounded = BoundedAbsoluteInterval::new(
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
    );
    assert_eq!(
        EmptiableAbsoluteInterval::from(bounded.clone()),
        AbsoluteInterval::Bounded(bounded).to_emptiable()
    );
    Ok(())
}

#[test]
fn from_half_bounded_interval() -> Result<(), Box<dyn Error>> {
    let half_bounded =
        HalfBoundedAbsoluteInterval::new_from_time("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture);
    assert_eq!(
        EmptiableAbsoluteInterval::from(half_bounded.clone()),
        AbsoluteInterval::HalfBounded(half_bounded).to_emptiable()
    );
    Ok(())
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        EmptiableAbsoluteInterval::from(UnboundedInterval),
        AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable()
    );
}

#[test]
fn from_empty_interval() {
    assert_eq!(
        EmptiableAbsoluteInterval::from(EmptyInterval),
        EmptiableAbsoluteInterval::Empty(EmptyInterval)
    );
}

mod from_bound_pair {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsoluteInterval::from(AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )),
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable(),
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsoluteInterval::from(AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture
            )),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable(),
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsoluteInterval::from(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            EmptiableAbsoluteInterval::from(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture
            )),
            AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable()
        );
    }
}

mod from_emptiable_bound_pair {
    use super::*;

    #[test]
    fn bound_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsoluteInterval::from(
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                )
                .to_emptiable()
            ),
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable(),
        );
        Ok(())
    }

    #[test]
    fn bound_half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsoluteInterval::from(
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable(),
        );
        Ok(())
    }

    #[test]
    fn bound_half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsoluteInterval::from(
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                )
                .to_emptiable()
            ),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
        );
        Ok(())
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            EmptiableAbsoluteInterval::from(
                AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
                    .to_emptiable()
            ),
            AbsoluteInterval::Unbounded(UnboundedInterval).to_emptiable()
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableAbsoluteInterval::from(EmptiableAbsoluteBoundPair::Empty),
            EmptiableAbsoluteInterval::Empty(EmptyInterval)
        );
    }
}

#[test]
fn from_interval() -> Result<(), Box<dyn Error>> {
    let interval =
        HalfBoundedAbsoluteInterval::new_from_time("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture)
            .to_interval();

    assert_eq!(
        EmptiableAbsoluteInterval::from(interval.clone()),
        EmptiableAbsoluteInterval::Bound(interval)
    );
    Ok(())
}

#[test]
fn from_unit_val() {
    assert_eq!(
        EmptiableAbsoluteInterval::from(()),
        EmptiableAbsoluteInterval::Empty(EmptyInterval)
    );
}

use std::cmp::Ordering;
use std::error::Error;
use std::time::Duration;

use jiff::Timestamp;

use super::emptiable_interval::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    HalfBoundedAbsInterval,
    HasEmptiableAbsBoundPair,
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
        EmptiableAbsInterval::from_range(start..),
        HalfBoundedAbsInterval::new_from_time(start, OpeningDirection::ToFuture).to_emptiable_interval()
    );
    Ok(())
}

#[test]
fn bound() -> Result<(), Box<dyn Error>> {
    let interval =
        HalfBoundedAbsInterval::new_from_time("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture);

    assert_eq!(
        interval.clone().to_emptiable_interval().bound(),
        Some(interval.to_interval())
    );
    assert_eq!(EmptiableAbsInterval::Empty(EmptyInterval).bound(), None);
    Ok(())
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn bounded_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(&AbsInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn bounded_empty() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture,
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .ord_by_start_and_inv_length(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn unbounded_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(
                    &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(&AbsInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Equal
        );
    }

    #[test]
    fn unbounded_empty() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .ord_by_start_and_inv_length(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn empty_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsInterval::Empty(EmptyInterval).ord_by_start_and_inv_length(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            EmptiableAbsInterval::Empty(EmptyInterval).ord_by_start_and_inv_length(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            EmptiableAbsInterval::Empty(EmptyInterval)
                .ord_by_start_and_inv_length(&AbsInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Less
        );
    }

    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableAbsInterval::Empty(EmptyInterval)
                .ord_by_start_and_inv_length(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Equal
        );
    }
}

mod duration {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable().duration(),
            IntervalDuration::Infinite
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableAbsInterval::Empty(EmptyInterval).duration(),
            IntervalDuration::Finite(Duration::ZERO, Epsilon::None)
        );
    }
}

mod relativity {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .relativity(),
            Relativity::Abs
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .relativity(),
            Relativity::Abs
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable().relativity(),
            Relativity::Any
        );
    }

    #[test]
    fn empty() {
        assert_eq!(EmptiableAbsInterval::Empty(EmptyInterval).relativity(), Relativity::Any);
    }
}

mod openness {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable().openness(),
            Openness::Unbounded
        );
    }

    #[test]
    fn empty() {
        assert_eq!(EmptiableAbsInterval::Empty(EmptyInterval).openness(), Openness::Empty);
    }
}

mod emptiable_abs_bound_pair {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .emptiable_abs_bound_pair(),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )
            .to_emptiable()
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .emptiable_abs_bound_pair(),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )
            .to_emptiable()
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .emptiable_abs_bound_pair(),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableAbsInterval::Empty(EmptyInterval).emptiable_abs_bound_pair(),
            EmptiableAbsBoundPair::Empty
        );
    }
}

mod partial_abs_start {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .partial_abs_start(),
            Some(AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .partial_abs_start(),
            Some(AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .partial_abs_start(),
            Some(AbsStartBound::InfinitePast)
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .partial_abs_start(),
            Some(AbsStartBound::InfinitePast)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(EmptiableAbsInterval::Empty(EmptyInterval).partial_abs_start(), None);
    }
}

mod partial_abs_end {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .partial_abs_end(),
            Some(AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .partial_abs_end(),
            Some(AbsEndBound::InfiniteFuture)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .partial_abs_end(),
            Some(AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound())
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .partial_abs_end(),
            Some(AbsEndBound::InfiniteFuture)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(EmptiableAbsInterval::Empty(EmptyInterval).partial_abs_end(), None);
    }
}

mod is_empty {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert!(
            !AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            !AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
        assert!(!AbsInterval::Unbounded(UnboundedInterval).to_emptiable().is_empty());
    }

    #[test]
    fn empty() {
        assert!(EmptiableAbsInterval::Empty(EmptyInterval).is_empty());
    }
}

mod ord {
    use super::*;

    #[test]
    fn bounded_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(&AbsInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn bounded_empty() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .to_emptiable()
            .cmp(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture,
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .to_emptiable()
            .cmp(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn unbounded_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable().cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .cmp(&AbsInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Equal
        );
    }

    #[test]
    fn unbounded_empty() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .to_emptiable()
                .cmp(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Greater
        );
    }

    #[test]
    fn empty_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsInterval::Empty(EmptyInterval).cmp(
                &AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            EmptiableAbsInterval::Empty(EmptyInterval).cmp(
                &AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            EmptiableAbsInterval::Empty(EmptyInterval).cmp(&AbsInterval::Unbounded(UnboundedInterval).to_emptiable()),
            Ordering::Less
        );
    }

    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableAbsInterval::Empty(EmptyInterval).cmp(&EmptiableAbsInterval::Empty(EmptyInterval)),
            Ordering::Equal
        );
    }
}

#[test]
fn from_bounded_interval() -> Result<(), Box<dyn Error>> {
    let bounded = BoundedAbsInterval::from_times(
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
    );
    assert_eq!(
        EmptiableAbsInterval::from(bounded.clone()),
        AbsInterval::Bounded(bounded).to_emptiable()
    );
    Ok(())
}

#[test]
fn from_half_bounded_interval() -> Result<(), Box<dyn Error>> {
    let half_bounded =
        HalfBoundedAbsInterval::new_from_time("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture);
    assert_eq!(
        EmptiableAbsInterval::from(half_bounded.clone()),
        AbsInterval::HalfBounded(half_bounded).to_emptiable()
    );
    Ok(())
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        EmptiableAbsInterval::from(UnboundedInterval),
        AbsInterval::Unbounded(UnboundedInterval).to_emptiable()
    );
}

#[test]
fn from_empty_interval() {
    assert_eq!(
        EmptiableAbsInterval::from(EmptyInterval),
        EmptiableAbsInterval::Empty(EmptyInterval)
    );
}

mod from_bound_pair {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsInterval::from(AbsBoundPair::new(
                AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )),
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            EmptiableAbsInterval::from(AbsBoundPair::new(
                AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            EmptiableAbsInterval::from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            EmptiableAbsInterval::from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsEndBound::InfiniteFuture
            )),
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable()
        );
    }
}

mod from_emptiable_bound_pair {
    use super::*;

    #[test]
    fn bound_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsInterval::from(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                )
                .to_emptiable()
            ),
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
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
            EmptiableAbsInterval::from(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            EmptiableAbsInterval::from(
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                )
                .to_emptiable()
            ),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
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
            EmptiableAbsInterval::from(
                AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
            ),
            AbsInterval::Unbounded(UnboundedInterval).to_emptiable()
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableAbsInterval::from(EmptiableAbsBoundPair::Empty),
            EmptiableAbsInterval::Empty(EmptyInterval)
        );
    }
}

#[test]
fn from_interval() -> Result<(), Box<dyn Error>> {
    let interval =
        HalfBoundedAbsInterval::new_from_time("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture)
            .to_interval();

    assert_eq!(
        EmptiableAbsInterval::from(interval.clone()),
        EmptiableAbsInterval::Bound(interval)
    );
    Ok(())
}

#[test]
fn from_unit_val() {
    assert_eq!(
        EmptiableAbsInterval::from(()),
        EmptiableAbsInterval::Empty(EmptyInterval)
    );
}

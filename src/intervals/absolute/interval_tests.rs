use std::cmp::Ordering;
use std::error::Error;
use std::ops::Bound;
use std::time::Duration;

use jiff::Timestamp;

use super::interval::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
    HasAbsBoundPair,
    HasEmptiableAbsBoundPair,
};
use crate::intervals::meta::{
    BoundInclusivity,
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
use crate::intervals::special::UnboundedInterval;

mod from_range {
    use super::*;

    #[test]
    fn included_included() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            AbsInterval::from_range(start..=end),
            AbsInterval::Bounded(BoundedAbsInterval::from_times(start, end))
        );
        Ok(())
    }

    #[test]
    fn included_excluded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            AbsInterval::from_range(start..end),
            AbsInterval::Bounded(BoundedAbsInterval::from_times_incl(
                start,
                BoundInclusivity::Inclusive,
                end,
                BoundInclusivity::Exclusive
            ))
        );
        Ok(())
    }

    #[test]
    fn included_unbounded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            AbsInterval::from_range(start..),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(start, OpeningDirection::ToFuture))
        );
        Ok(())
    }

    #[test]
    fn excluded_included() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            AbsInterval::from_range((Bound::Excluded(start), Bound::Included(end))),
            AbsInterval::Bounded(BoundedAbsInterval::from_times_incl(
                start,
                BoundInclusivity::Exclusive,
                end,
                BoundInclusivity::Inclusive
            ))
        );
        Ok(())
    }

    #[test]
    fn excluded_excluded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            AbsInterval::from_range((Bound::Excluded(start), Bound::Excluded(end))),
            AbsInterval::Bounded(BoundedAbsInterval::from_times_incl(
                start,
                BoundInclusivity::Exclusive,
                end,
                BoundInclusivity::Exclusive
            ))
        );
        Ok(())
    }

    #[test]
    fn excluded_unbounded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            AbsInterval::from_range((Bound::Excluded(start), Bound::Unbounded)),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time_incl(
                start,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture
            ))
        );
        Ok(())
    }

    #[test]
    fn unbounded_included() -> Result<(), Box<dyn Error>> {
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            AbsInterval::from_range(..=end),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(end, OpeningDirection::ToPast))
        );
        Ok(())
    }

    #[test]
    fn unbounded_excluded() -> Result<(), Box<dyn Error>> {
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            AbsInterval::from_range(..end),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time_incl(
                end,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast
            ))
        );
        Ok(())
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(AbsInterval::from_range(..), AbsInterval::Unbounded(UnboundedInterval));
    }
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
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?
            ))),
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
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?
            ))),
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
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))),
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
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            ))),
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
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))),
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
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))),
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
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))),
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
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture,
            ))),
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
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))),
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
            .ord_by_start_and_inv_length(&AbsInterval::Unbounded(UnboundedInterval)),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?
            ))),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_less_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture,
            ))
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_less_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture,
            ))),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_equal_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_greater_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn unbounded_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&AbsInterval::Bounded(
                BoundedAbsInterval::from_times(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?
                )
            )),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn unbounded_half_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&AbsInterval::HalfBounded(
                HalfBoundedAbsInterval::from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToPast
                )
            )),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn unbounded_half_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&AbsInterval::HalfBounded(
                HalfBoundedAbsInterval::from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                )
            )),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval)
                .ord_by_start_and_inv_length(&AbsInterval::Unbounded(UnboundedInterval)),
            Ordering::Equal
        );
    }
}

#[test]
fn bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsInterval::Bounded(BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        ))
        .bounded(),
        Some(BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        ))
    );
    assert_eq!(
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            OpeningDirection::ToFuture
        ))
        .bounded(),
        None
    );
    assert_eq!(AbsInterval::Unbounded(UnboundedInterval).bounded(), None);
    Ok(())
}

#[test]
fn half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsInterval::Bounded(BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        ))
        .half_bounded(),
        None
    );
    assert_eq!(
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            OpeningDirection::ToFuture
        ))
        .half_bounded(),
        Some(HalfBoundedAbsInterval::from_time(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            OpeningDirection::ToFuture
        ))
    );
    assert_eq!(AbsInterval::Unbounded(UnboundedInterval).half_bounded(), None);
    Ok(())
}

#[test]
fn unbounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsInterval::Bounded(BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        ))
        .unbounded(),
        None
    );
    assert_eq!(
        AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            OpeningDirection::ToFuture
        ))
        .unbounded(),
        None
    );
    assert_eq!(
        AbsInterval::Unbounded(UnboundedInterval).unbounded(),
        Some(UnboundedInterval)
    );
    Ok(())
}

#[test]
fn to_emptiable() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsInterval::Bounded(BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        ))
        .to_emptiable(),
        EmptiableAbsInterval::Bound(AbsInterval::Bounded(BoundedAbsInterval::from_times(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        )))
    );
    Ok(())
}

mod abs_bound_pair {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .abs_bound_pair(),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .abs_bound_pair(),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).abs_bound_pair(),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture)
        );
    }
}

mod abs_start {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .abs_start(),
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .abs_start(),
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .abs_start(),
            AbsStartBound::InfinitePast
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).abs_start(),
            AbsStartBound::InfinitePast
        );
    }
}

mod abs_end {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .abs_end(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .abs_end(),
            AbsEndBound::InfiniteFuture
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .abs_end(),
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).abs_end(),
            AbsEndBound::InfiniteFuture
        );
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
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
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
            AbsInterval::Unbounded(UnboundedInterval).emptiable_abs_bound_pair(),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
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
            .partial_abs_start(),
            Some(AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .partial_abs_start(),
            Some(AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .partial_abs_start(),
            Some(AbsStartBound::InfinitePast)
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).partial_abs_start(),
            Some(AbsStartBound::InfinitePast)
        );
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
            .partial_abs_end(),
            Some(AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .partial_abs_end(),
            Some(AbsEndBound::InfiniteFuture)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .partial_abs_end(),
            Some(AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound())
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).partial_abs_end(),
            Some(AbsEndBound::InfiniteFuture)
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
            .duration(),
            IntervalDuration::Finite(Duration::from_hours(24), Epsilon::None)
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .duration(),
            IntervalDuration::Infinite
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).duration(),
            IntervalDuration::Infinite
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
            .relativity(),
            Relativity::Abs
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .relativity(),
            Relativity::Abs
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(AbsInterval::Unbounded(UnboundedInterval).relativity(), Relativity::Any);
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
            .openness(),
            Openness::Bounded
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .openness(),
            Openness::HalfBounded
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).openness(),
            Openness::Unbounded
        );
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
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?
            ))),
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
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?
            ))),
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
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))),
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
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            ))),
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
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))),
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
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))),
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
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))),
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
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture,
            ))),
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
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))),
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
            .cmp(&AbsInterval::Unbounded(UnboundedInterval)),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?
            ))),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_less_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture,
            ))
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_less_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture,
            ))),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_equal_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_greater_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn unbounded_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).cmp(&AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn unbounded_half_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).cmp(&AbsInterval::HalfBounded(
                HalfBoundedAbsInterval::from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToPast
                )
            )),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn unbounded_half_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).cmp(&AbsInterval::HalfBounded(
                HalfBoundedAbsInterval::from_time(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                )
            )),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            AbsInterval::Unbounded(UnboundedInterval).cmp(&AbsInterval::Unbounded(UnboundedInterval)),
            Ordering::Equal
        );
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
            .is_empty()
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert!(
            !AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .is_empty()
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert!(!AbsInterval::Unbounded(UnboundedInterval).is_empty());
    }
}

#[test]
fn from_bounded_interval() -> Result<(), Box<dyn Error>> {
    let bounded = BoundedAbsInterval::from_times(
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
    );
    assert_eq!(AbsInterval::from(bounded.clone()), AbsInterval::Bounded(bounded));
    Ok(())
}

#[test]
fn from_half_bounded_interval() -> Result<(), Box<dyn Error>> {
    let half_bounded =
        HalfBoundedAbsInterval::from_time("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture);
    assert_eq!(
        AbsInterval::from(half_bounded.clone()),
        AbsInterval::HalfBounded(half_bounded)
    );
    Ok(())
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        AbsInterval::from(UnboundedInterval),
        AbsInterval::Unbounded(UnboundedInterval)
    );
}

mod from_bound_pair {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::from(AbsBoundPair::new(
                AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )),
            AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            )),
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::from(AbsBoundPair::new(
                AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            )),
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )),
            AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsInterval::from(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsEndBound::InfiniteFuture
            )),
            AbsInterval::Unbounded(UnboundedInterval)
        );
    }
}

mod try_from_emptiable_bound_pair {
    use super::*;

    #[test]
    fn bound_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::try_from(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                )
                .to_emptiable()
            ),
            Ok(AbsInterval::Bounded(BoundedAbsInterval::from_times(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))),
        );
        Ok(())
    }

    #[test]
    fn bound_half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::try_from(
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            Ok(AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))),
        );
        Ok(())
    }

    #[test]
    fn bound_half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsInterval::try_from(
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                )
                .to_emptiable()
            ),
            Ok(AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            )))
        );
        Ok(())
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            AbsInterval::try_from(
                AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
            ),
            Ok(AbsInterval::Unbounded(UnboundedInterval))
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            AbsInterval::try_from(EmptiableAbsBoundPair::Empty),
            Err(AbsIntervalFromEmptiableAbsBoundPairError)
        );
    }
}

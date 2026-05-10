use std::cmp::Ordering;
use std::error::Error;
use std::ops::Bound;
use std::time::Duration;

use jiff::Timestamp;

use super::interval::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
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
            AbsoluteInterval::from_range(start..=end),
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(start, end))
        );
        Ok(())
    }

    #[test]
    fn included_excluded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            AbsoluteInterval::from_range(start..end),
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
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
            AbsoluteInterval::from_range(start..),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(start, OpeningDirection::ToFuture))
        );
        Ok(())
    }

    #[test]
    fn excluded_included() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            AbsoluteInterval::from_range((Bound::Excluded(start), Bound::Included(end))),
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
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
            AbsoluteInterval::from_range((Bound::Excluded(start), Bound::Excluded(end))),
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_with_inclusivity(
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
            AbsoluteInterval::from_range((Bound::Excluded(start), Bound::Unbounded)),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
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
            AbsoluteInterval::from_range(..=end),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(end, OpeningDirection::ToPast))
        );
        Ok(())
    }

    #[test]
    fn unbounded_excluded() -> Result<(), Box<dyn Error>> {
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            AbsoluteInterval::from_range(..end),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                end,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToPast
            ))
        );
        Ok(())
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            AbsoluteInterval::from_range(..),
            AbsoluteInterval::Unbounded(UnboundedInterval)
        );
    }
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
            .ord_by_start_and_inv_length(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                )
            )),
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
            .ord_by_start_and_inv_length(&AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                )
            )),
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
            .ord_by_start_and_inv_length(&AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture,
                )
            )),
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
            .ord_by_start_and_inv_length(&AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToPast
                )
            )),
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
            .ord_by_start_and_inv_length(&AbsoluteInterval::Unbounded(UnboundedInterval)),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture,
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                )
            )),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_less_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                )
            )),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture,
                )
            )),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_equal_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToPast
                )
            )),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToFuture
                )
            )),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_half_bounded_start_greater_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .ord_by_start_and_inv_length(&AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    OpeningDirection::ToPast
                )
            )),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn unbounded_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&AbsoluteInterval::Bounded(
                BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Unbounded(UnboundedInterval).ord_by_start_and_inv_length(&AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Unbounded(UnboundedInterval)
                .ord_by_start_and_inv_length(&AbsoluteInterval::Unbounded(UnboundedInterval)),
            Ordering::Equal
        );
    }
}

#[test]
fn bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        ))
        .bounded(),
        Some(BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        ))
    );
    assert_eq!(
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            OpeningDirection::ToFuture
        ))
        .bounded(),
        None
    );
    assert_eq!(AbsoluteInterval::Unbounded(UnboundedInterval).bounded(), None);
    Ok(())
}

#[test]
fn half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        ))
        .half_bounded(),
        None
    );
    assert_eq!(
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            OpeningDirection::ToFuture
        ))
        .half_bounded(),
        Some(HalfBoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            OpeningDirection::ToFuture
        ))
    );
    assert_eq!(AbsoluteInterval::Unbounded(UnboundedInterval).half_bounded(), None);
    Ok(())
}

#[test]
fn unbounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        ))
        .unbounded(),
        None
    );
    assert_eq!(
        AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            OpeningDirection::ToFuture
        ))
        .unbounded(),
        None
    );
    assert_eq!(
        AbsoluteInterval::Unbounded(UnboundedInterval).unbounded(),
        Some(UnboundedInterval)
    );
    Ok(())
}

#[test]
fn to_emptiable() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?
        ))
        .to_emptiable(),
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .abs_bound_pair(),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .abs_bound_pair(),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture
            )
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval).abs_bound_pair(),
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
        );
    }
}

mod abs_start {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .abs_start(),
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .abs_start(),
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .abs_start(),
            AbsoluteStartBound::InfinitePast
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval).abs_start(),
            AbsoluteStartBound::InfinitePast
        );
    }
}

mod abs_end {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .abs_end(),
            AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .abs_end(),
            AbsoluteEndBound::InfiniteFuture
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .abs_end(),
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval).abs_end(),
            AbsoluteEndBound::InfiniteFuture
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
            .emptiable_abs_bound_pair(),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )
            .to_emptiable()
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .emptiable_abs_bound_pair(),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture
            )
            .to_emptiable()
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval).emptiable_abs_bound_pair(),
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).to_emptiable()
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
            .partial_abs_start(),
            Some(AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .partial_abs_start(),
            Some(AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .partial_abs_start(),
            Some(AbsoluteStartBound::InfinitePast)
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval).partial_abs_start(),
            Some(AbsoluteStartBound::InfinitePast)
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
            .partial_abs_end(),
            Some(AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .partial_abs_end(),
            Some(AbsoluteEndBound::InfiniteFuture)
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .partial_abs_end(),
            Some(AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound())
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval).partial_abs_end(),
            Some(AbsoluteEndBound::InfiniteFuture)
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
            .duration(),
            IntervalDuration::Finite(Duration::from_hours(24), Epsilon::None)
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Unbounded(UnboundedInterval).duration(),
            IntervalDuration::Infinite
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
            .relativity(),
            Relativity::Absolute
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .relativity(),
            Relativity::Absolute
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsoluteInterval::Unbounded(UnboundedInterval).relativity(),
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
            .openness(),
            Openness::Bounded
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Unbounded(UnboundedInterval).openness(),
            Openness::Unbounded
        );
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
            .cmp(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .cmp(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .cmp(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?
            ))
            .cmp(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
            ))
            .cmp(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .cmp(&AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .cmp(&AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
            ))
            .cmp(&AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
            ))
            .cmp(&AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))
            .cmp(&AbsoluteInterval::Unbounded(UnboundedInterval)),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn half_bounded_bounded_start_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .cmp(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture,
            ))
            .cmp(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .cmp(&AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
            .cmp(&AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .cmp(&AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Unbounded(UnboundedInterval).cmp(&AbsoluteInterval::Bounded(
                BoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Unbounded(UnboundedInterval).cmp(&AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Unbounded(UnboundedInterval).cmp(&AbsoluteInterval::HalfBounded(
                HalfBoundedAbsoluteInterval::new(
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
            AbsoluteInterval::Unbounded(UnboundedInterval).cmp(&AbsoluteInterval::Unbounded(UnboundedInterval)),
            Ordering::Equal
        );
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
            .is_empty()
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        assert!(
            !AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
            .is_empty()
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert!(!AbsoluteInterval::Unbounded(UnboundedInterval).is_empty());
    }
}

#[test]
fn from_bounded_interval() -> Result<(), Box<dyn Error>> {
    let bounded = BoundedAbsoluteInterval::new(
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
    );
    assert_eq!(
        AbsoluteInterval::from(bounded.clone()),
        AbsoluteInterval::Bounded(bounded)
    );
    Ok(())
}

#[test]
fn from_half_bounded_interval() -> Result<(), Box<dyn Error>> {
    let half_bounded =
        HalfBoundedAbsoluteInterval::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture);
    assert_eq!(
        AbsoluteInterval::from(half_bounded.clone()),
        AbsoluteInterval::HalfBounded(half_bounded)
    );
    Ok(())
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        AbsoluteInterval::from(UnboundedInterval),
        AbsoluteInterval::Unbounded(UnboundedInterval)
    );
}

mod from_bound_pair {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::from(AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )),
            AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            )),
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::from(AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture
            )),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            )),
        );
        Ok(())
    }

    #[test]
    fn half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::from(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )),
            AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsoluteInterval::from(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture
            )),
            AbsoluteInterval::Unbounded(UnboundedInterval)
        );
    }
}

mod try_from_emptiable_bound_pair {
    use super::*;

    #[test]
    fn bound_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::try_from(
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                )
                .to_emptiable()
            ),
            Ok(AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?
            ))),
        );
        Ok(())
    }

    #[test]
    fn bound_half_bounded_to_future() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::try_from(
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture
                )
                .to_emptiable()
            ),
            Ok(AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))),
        );
        Ok(())
    }

    #[test]
    fn bound_half_bounded_to_past() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteInterval::try_from(
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                )
                .to_emptiable()
            ),
            Ok(AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            )))
        );
        Ok(())
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            AbsoluteInterval::try_from(
                AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
                    .to_emptiable()
            ),
            Ok(AbsoluteInterval::Unbounded(UnboundedInterval))
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            AbsoluteInterval::try_from(EmptiableAbsoluteBoundPair::Empty),
            Err(AbsoluteIntervalFromEmptiableAbsoluteBoundPairError)
        );
    }
}

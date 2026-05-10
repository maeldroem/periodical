use std::error::Error;
use std::ops::Bound;

use jiff::Timestamp;

use super::half_bounded_interval::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    EmptiableAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::{
    BoundInclusivity,
    Duration as IntervalDuration,
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
fn new() -> Result<(), Box<dyn Error>> {
    let interval =
        HalfBoundedAbsoluteInterval::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture);

    assert_eq!(interval.reference(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.opening_direction(), OpeningDirection::ToFuture);
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Inclusive);

    Ok(())
}

#[test]
fn new_with_inclusivity() -> Result<(), Box<dyn Error>> {
    let interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        OpeningDirection::ToPast,
    );

    assert_eq!(interval.reference(), "2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    assert_eq!(interval.opening_direction(), OpeningDirection::ToPast);
    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);

    Ok(())
}

mod try_from_range {
    use super::*;

    #[test]
    fn included_included() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from_range(start..=end),
            Err(HalfBoundedAbsoluteIntervalTryFromRangeError)
        );
        Ok(())
    }

    #[test]
    fn included_excluded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from_range(start..end),
            Err(HalfBoundedAbsoluteIntervalTryFromRangeError)
        );
        Ok(())
    }

    #[test]
    fn included_unbounded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from_range(start..),
            Ok(HalfBoundedAbsoluteInterval::new(start, OpeningDirection::ToFuture))
        );
        Ok(())
    }

    #[test]
    fn excluded_included() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from_range((Bound::Excluded(start), Bound::Included(end))),
            Err(HalfBoundedAbsoluteIntervalTryFromRangeError)
        );
        Ok(())
    }

    #[test]
    fn excluded_excluded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from_range((Bound::Excluded(start), Bound::Excluded(end))),
            Err(HalfBoundedAbsoluteIntervalTryFromRangeError)
        );
        Ok(())
    }

    #[test]
    fn excluded_unbounded() -> Result<(), Box<dyn Error>> {
        let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from_range((Bound::Excluded(start), Bound::Unbounded)),
            Ok(HalfBoundedAbsoluteInterval::new_with_inclusivity(
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
            HalfBoundedAbsoluteInterval::try_from_range(..=end),
            Ok(HalfBoundedAbsoluteInterval::new(end, OpeningDirection::ToPast))
        );
        Ok(())
    }

    #[test]
    fn unbounded_excluded() -> Result<(), Box<dyn Error>> {
        let end = "2026-01-02 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from_range(..end),
            Ok(HalfBoundedAbsoluteInterval::new_with_inclusivity(
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
            HalfBoundedAbsoluteInterval::try_from_range(..),
            Err(HalfBoundedAbsoluteIntervalTryFromRangeError)
        );
    }
}

#[test]
fn reference() -> Result<(), Box<dyn Error>> {
    let reference = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    let interval = HalfBoundedAbsoluteInterval::new(reference, OpeningDirection::ToFuture);

    assert_eq!(interval.reference(), reference);
    Ok(())
}

#[test]
fn opening_direction() -> Result<(), Box<dyn Error>> {
    let to_future =
        HalfBoundedAbsoluteInterval::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture);
    let to_past =
        HalfBoundedAbsoluteInterval::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToPast);

    assert_eq!(to_future.opening_direction(), OpeningDirection::ToFuture);
    assert_eq!(to_past.opening_direction(), OpeningDirection::ToPast);

    Ok(())
}

#[test]
fn reference_inclusivity() -> Result<(), Box<dyn Error>> {
    let interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    assert_eq!(interval.reference_inclusivity(), BoundInclusivity::Exclusive);
    Ok(())
}

#[test]
fn set_reference() -> Result<(), Box<dyn Error>> {
    let mut interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference("2025-01-02 00:00:00Z".parse::<Timestamp>()?);

    assert_eq!(
        interval,
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )
    );

    Ok(())
}

#[test]
fn set_reference_inclusivity() -> Result<(), Box<dyn Error>> {
    let mut interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_reference_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(
        interval,
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
            OpeningDirection::ToFuture,
        )
    );

    Ok(())
}

#[test]
fn set_opening_direction() -> Result<(), Box<dyn Error>> {
    let mut interval = HalfBoundedAbsoluteInterval::new_with_inclusivity(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
        OpeningDirection::ToFuture,
    );

    interval.set_opening_direction(OpeningDirection::ToPast);

    assert_eq!(
        interval,
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        )
    );

    Ok(())
}

#[test]
fn to_interval() -> Result<(), Box<dyn Error>> {
    let half_bounded =
        HalfBoundedAbsoluteInterval::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture);

    assert_eq!(
        half_bounded.clone().to_interval(),
        AbsoluteInterval::HalfBounded(half_bounded)
    );
    Ok(())
}

#[test]
fn to_emptiable_interval() -> Result<(), Box<dyn Error>> {
    let half_bounded =
        HalfBoundedAbsoluteInterval::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture);

    assert_eq!(
        half_bounded.clone().to_emptiable_interval(),
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::HalfBounded(half_bounded))
    );
    Ok(())
}

#[test]
fn openness() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture)
            .openness(),
        Openness::HalfBounded
    );
    Ok(())
}

#[test]
fn relativity() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture)
            .relativity(),
        Relativity::Absolute
    );
    Ok(())
}

#[test]
fn duration() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture)
            .duration(),
        IntervalDuration::Infinite
    );
    Ok(())
}

#[test]
fn abs_bound_pair() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture)
            .abs_bound_pair(),
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture
        )
    );
    Ok(())
}

#[test]
fn abs_start() -> Result<(), Box<dyn Error>> {
    let reference = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        HalfBoundedAbsoluteInterval::new(reference, OpeningDirection::ToFuture).abs_start(),
        AbsoluteFiniteBound::new(reference).to_start_bound()
    );
    assert_eq!(
        HalfBoundedAbsoluteInterval::new(reference, OpeningDirection::ToPast).abs_start(),
        AbsoluteStartBound::InfinitePast
    );
    Ok(())
}

#[test]
fn abs_end() -> Result<(), Box<dyn Error>> {
    let reference = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        HalfBoundedAbsoluteInterval::new(reference, OpeningDirection::ToFuture).abs_end(),
        AbsoluteEndBound::InfiniteFuture
    );
    assert_eq!(
        HalfBoundedAbsoluteInterval::new(reference, OpeningDirection::ToPast).abs_end(),
        AbsoluteFiniteBound::new(reference).to_end_bound()
    );
    Ok(())
}

#[test]
fn emptiable_abs_bound_pair() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture)
            .emptiable_abs_bound_pair(),
        EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture
        ))
    );
    Ok(())
}

#[test]
fn partial_abs_start() -> Result<(), Box<dyn Error>> {
    let reference = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        HalfBoundedAbsoluteInterval::new(reference, OpeningDirection::ToFuture).partial_abs_start(),
        Some(AbsoluteFiniteBound::new(reference).to_start_bound())
    );
    assert_eq!(
        HalfBoundedAbsoluteInterval::new(reference, OpeningDirection::ToPast).partial_abs_start(),
        Some(AbsoluteStartBound::InfinitePast)
    );
    Ok(())
}

#[test]
fn partial_abs_end() -> Result<(), Box<dyn Error>> {
    let reference = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        HalfBoundedAbsoluteInterval::new(reference, OpeningDirection::ToFuture).partial_abs_end(),
        Some(AbsoluteEndBound::InfiniteFuture)
    );
    assert_eq!(
        HalfBoundedAbsoluteInterval::new(reference, OpeningDirection::ToPast).partial_abs_end(),
        Some(AbsoluteFiniteBound::new(reference).to_end_bound())
    );
    Ok(())
}

#[test]
fn is_empty() -> Result<(), Box<dyn Error>> {
    assert!(
        !HalfBoundedAbsoluteInterval::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture)
            .is_empty()
    );
    Ok(())
}

#[test]
fn from_timestamp_opening_direction_pair() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from(("2025-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture)),
        HalfBoundedAbsoluteInterval::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture),
    );

    Ok(())
}

#[test]
fn from_timestamp_inclusivity_opening_direction_triple() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from((
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast
        )),
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );

    Ok(())
}

#[test]
fn from_range_from() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from("2025-01-01 00:00:00Z".parse::<Timestamp>()?..),
        HalfBoundedAbsoluteInterval::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture),
    );

    Ok(())
}

#[test]
fn from_range_to() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from(.."2025-01-01 00:00:00Z".parse::<Timestamp>()?),
        HalfBoundedAbsoluteInterval::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
            OpeningDirection::ToPast,
        ),
    );

    Ok(())
}

#[test]
fn from_range_to_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        HalfBoundedAbsoluteInterval::from(..="2025-01-01 00:00:00Z".parse::<Timestamp>()?),
        HalfBoundedAbsoluteInterval::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToPast),
    );

    Ok(())
}

mod try_from_bound_pair {
    use super::*;

    #[test]
    fn finite_finite() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )),
            Err(HalfBoundedAbsoluteIntervalTryFromAbsoluteBoundPairError)
        );
        Ok(())
    }

    #[test]
    fn finite_infinite() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture
            )),
            Ok(HalfBoundedAbsoluteInterval::new(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToFuture
            ))
        );
        Ok(())
    }

    #[test]
    fn infinite_finite() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
            )),
            Ok(HalfBoundedAbsoluteInterval::new(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                OpeningDirection::ToPast
            ))
        );
        Ok(())
    }

    #[test]
    fn infinite_infinite() {
        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture
            )),
            Err(HalfBoundedAbsoluteIntervalTryFromAbsoluteBoundPairError)
        );
    }
}

mod try_from_interval {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        let bounded = BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from(bounded.to_interval()),
            Err(HalfBoundedAbsoluteIntervalTryFromAbsoluteIntervalError)
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        let half_bounded =
            HalfBoundedAbsoluteInterval::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture);

        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from(half_bounded.clone().to_interval()),
            Ok(half_bounded)
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from(UnboundedInterval.to_abs_interval()),
            Err(HalfBoundedAbsoluteIntervalTryFromAbsoluteIntervalError)
        );
    }
}

mod try_from_emptiable_interval {
    use super::*;

    #[test]
    fn bound_bounded() -> Result<(), Box<dyn Error>> {
        let bounded = BoundedAbsoluteInterval::new(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
        );

        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from(bounded.to_emptiable_interval()),
            Err(HalfBoundedAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError)
        );
        Ok(())
    }

    #[test]
    fn bound_half_bounded() -> Result<(), Box<dyn Error>> {
        let half_bounded =
            HalfBoundedAbsoluteInterval::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?, OpeningDirection::ToFuture);

        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from(half_bounded.clone().to_emptiable_interval()),
            Ok(half_bounded)
        );
        Ok(())
    }

    #[test]
    fn bound_unbounded() {
        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from(UnboundedInterval.to_emptiable_abs_interval()),
            Err(HalfBoundedAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError)
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            HalfBoundedAbsoluteInterval::try_from(EmptyInterval.to_emptiable_abs_interval()),
            Err(HalfBoundedAbsoluteIntervalTryFromEmptiableAbsoluteIntervalError)
        );
    }
}

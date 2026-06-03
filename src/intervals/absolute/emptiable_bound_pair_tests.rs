use std::cmp::Ordering;
use std::error::Error;
use std::time::Duration;

use jiff::Timestamp;

use super::emptiable_bound_pair::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsInterval,
    HalfBoundedAbsInterval,
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
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[test]
fn from_range() -> Result<(), Box<dyn Error>> {
    let start = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

    assert_eq!(
        EmptiableAbsBoundPair::from_range(start..),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new(start).to_start_bound(),
            AbsEndBound::InfiniteFuture
        )
        .to_emptiable()
    );
    Ok(())
}

mod ord_by_start_and_inv_length {
    use super::*;

    #[test]
    fn bound_bound_less_start() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn bound_bound_greater_start() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn bound_bound_less_start_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn bound_bound_greater_start_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_less_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_equal_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_greater_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_less_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_greater_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_equal_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end_inf() {
        let bound_pair1 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_unbound() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = EmptiableAbsBoundPair::Empty;

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn unbound_bound() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = EmptiableAbsBoundPair::Empty;
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.ord_by_start_and_inv_length(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn unbound_unbound() {
        assert_eq!(
            EmptiableAbsBoundPair::Empty.ord_by_start_and_inv_length(&EmptiableAbsBoundPair::Empty),
            Ordering::Equal
        );
    }
}

#[test]
fn bound() -> Result<(), Box<dyn Error>> {
    let bound_pair = AbsBoundPair::new(
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    );
    let emptiable_bound_pair = bound_pair.clone().to_emptiable();

    assert_eq!(emptiable_bound_pair.bound(), Some(bound_pair));
    assert_eq!(EmptiableAbsBoundPair::Empty.bound(), None);
    Ok(())
}

mod to_emptiable_interval {
    use super::*;

    #[test]
    fn bounded() -> Result<(), Box<dyn Error>> {
        let start = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_finite_start_bound();
        let end = AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();

        assert_eq!(
            AbsBoundPair::new(start.to_start_bound(), end.to_end_bound(),)
                .to_emptiable()
                .to_emptiable_interval(),
            EmptiableAbsInterval::Bound(AbsInterval::Bounded(BoundedAbsInterval::new(start, end)))
        );
        Ok(())
    }

    #[test]
    fn half_bounded() -> Result<(), Box<dyn Error>> {
        let reference = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;

        assert_eq!(
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(reference).to_start_bound(),
                AbsEndBound::InfiniteFuture
            )
            .to_emptiable()
            .to_emptiable_interval(),
            EmptiableAbsInterval::Bound(AbsInterval::HalfBounded(HalfBoundedAbsInterval::new_from_time(
                reference,
                OpeningDirection::ToFuture
            )))
        );
        Ok(())
    }

    #[test]
    fn unbounded() {
        assert_eq!(
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture)
                .to_emptiable()
                .to_emptiable_interval(),
            EmptiableAbsInterval::Bound(AbsInterval::Unbounded(UnboundedInterval))
        );
    }

    #[test]
    fn empty() {
        assert_eq!(
            EmptiableAbsBoundPair::Empty.to_emptiable_interval(),
            EmptiableAbsInterval::Empty(EmptyInterval)
        );
    }
}

#[test]
fn emptiable_abs_bound_pair() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_end_bound(),
        )
        .to_emptiable()
        .emptiable_abs_bound_pair(),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_end_bound(),
        )
        .to_emptiable()
    );
    Ok(())
}

#[test]
fn partial_abs_start() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_end_bound(),
        )
        .to_emptiable()
        .partial_abs_start(),
        Some(
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_start_bound()
        )
    );
    assert_eq!(EmptiableAbsBoundPair::Empty.partial_abs_start(), None);
    Ok(())
}

#[test]
fn partial_abs_end() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_end_bound(),
        )
        .to_emptiable()
        .partial_abs_end(),
        Some(
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_end_bound()
        )
    );
    assert_eq!(EmptiableAbsBoundPair::Empty.partial_abs_end(), None);
    Ok(())
}

#[test]
fn is_empty() {
    assert!(
        !AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture)
            .to_emptiable()
            .is_empty()
    );
    assert!(EmptiableAbsBoundPair::Empty.is_empty());
}

#[test]
fn duration() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
        )
        .to_emptiable()
        .duration(),
        IntervalDuration::Finite(Duration::from_hours(24), Epsilon::None)
    );
    assert_eq!(
        EmptiableAbsBoundPair::Empty.duration(),
        IntervalDuration::Finite(Duration::ZERO, Epsilon::None)
    );
    Ok(())
}

#[test]
fn openness() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
        )
        .to_emptiable()
        .openness(),
        Openness::Bounded
    );
    assert_eq!(EmptiableAbsBoundPair::Empty.openness(), Openness::Empty);
    Ok(())
}

#[test]
fn relativity() -> Result<(), Box<dyn Error>> {
    let bounded = AbsBoundPair::new(
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
    )
    .to_emptiable();
    let half_bounded = AbsBoundPair::new(
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        AbsEndBound::InfiniteFuture,
    )
    .to_emptiable();
    let unbounded = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();

    assert_eq!(bounded.relativity(), Relativity::Abs);
    assert_eq!(half_bounded.relativity(), Relativity::Abs);
    assert_eq!(unbounded.relativity(), Relativity::Any);
    assert_eq!(EmptiableAbsBoundPair::Empty.relativity(), Relativity::Any);
    Ok(())
}

mod ord {
    use super::*;

    #[test]
    fn bound_bound_equal_start_less_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_greater_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn bound_bound_less_start_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn bound_bound_greater_start_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_equal_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_greater_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_less_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_equal_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture,
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_inf_greater_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_inf_less_end_inf() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
        Ok(())
    }

    #[test]
    fn bound_bound_equal_start_inf_equal_end_inf() {
        let bound_pair1 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();
        let bound_pair2 = AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Equal);
    }

    #[test]
    fn bound_unbound() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();
        let bound_pair2 = EmptiableAbsBoundPair::Empty;

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn unbound_bound() -> Result<(), Box<dyn Error>> {
        let bound_pair1 = EmptiableAbsBoundPair::Empty;
        let bound_pair2 = AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        )
        .to_emptiable();

        assert_eq!(bound_pair1.cmp(&bound_pair2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn unbound_unbound() {
        assert_eq!(
            EmptiableAbsBoundPair::Empty.cmp(&EmptiableAbsBoundPair::Empty),
            Ordering::Equal
        );
    }
}

#[test]
fn from_opt_start_end() {
    assert_eq!(
        EmptiableAbsBoundPair::from(Some((AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture))),
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
    );
    assert_eq!(
        EmptiableAbsBoundPair::from(None::<(AbsStartBound, AbsEndBound)>),
        EmptiableAbsBoundPair::Empty
    );
}

#[test]
fn from_opt_start_opt_end_opt() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        EmptiableAbsBoundPair::from(Some((
            Some("2026-01-01 00:00:00Z".parse::<Timestamp>()?),
            Some("2026-01-02 00:00:00Z".parse::<Timestamp>()?)
        ))),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
        )
        .to_emptiable()
    );
    assert_eq!(
        EmptiableAbsBoundPair::from(None::<(Option<Timestamp>, Option<Timestamp>)>),
        EmptiableAbsBoundPair::Empty
    );
    Ok(())
}

#[test]
fn from_opt_start_incl_opt_end_incl_opt() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        EmptiableAbsBoundPair::from(Some((
            Some((
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )),
            Some((
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            ))
        ))),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_start_bound(),
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_end_bound()
        )
        .to_emptiable()
    );
    assert_eq!(
        EmptiableAbsBoundPair::from(
            None::<(
                Option<(Timestamp, BoundInclusivity)>,
                Option<(Timestamp, BoundInclusivity)>
            )>
        ),
        EmptiableAbsBoundPair::Empty
    );
    Ok(())
}

#[test]
fn from_bound_pair() {
    assert_eq!(
        EmptiableAbsBoundPair::from(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        )),
        EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
            AbsStartBound::InfinitePast,
            AbsEndBound::InfiniteFuture,
        )),
    );
}

#[test]
fn from_bounded_interval() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();

    assert_eq!(
        EmptiableAbsBoundPair::from(BoundedAbsInterval::new(start, end,)),
        AbsBoundPair::new(start.to_start_bound(), end.to_end_bound()).to_emptiable()
    );
    Ok(())
}

#[test]
fn from_half_bounded_interval() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        EmptiableAbsBoundPair::from(HalfBoundedAbsInterval::new_from_time(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            OpeningDirection::ToFuture,
        )),
        AbsBoundPair::new(
            AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsEndBound::InfiniteFuture
        )
        .to_emptiable()
    );
    Ok(())
}

#[test]
fn from_interval() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();

    assert_eq!(
        EmptiableAbsBoundPair::from(AbsInterval::Bounded(BoundedAbsInterval::new(start, end,))),
        AbsBoundPair::new(start.to_start_bound(), end.to_end_bound(),).to_emptiable()
    );
    Ok(())
}

#[test]
fn from_emptiable_interval() -> Result<(), Box<dyn Error>> {
    let start = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_finite_start_bound();
    let end = AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_finite_end_bound();
    assert_eq!(
        EmptiableAbsBoundPair::from(EmptiableAbsInterval::Bound(AbsInterval::Bounded(
            BoundedAbsInterval::new(start, end,)
        ))),
        AbsBoundPair::new(start.to_start_bound(), end.to_end_bound(),).to_emptiable()
    );
    assert_eq!(
        EmptiableAbsBoundPair::from(EmptiableAbsInterval::Empty(EmptyInterval)),
        EmptiableAbsBoundPair::Empty
    );
    Ok(())
}

#[test]
fn from_unbounded_interval() {
    assert_eq!(
        EmptiableAbsBoundPair::from(UnboundedInterval),
        AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).to_emptiable()
    );
}

#[test]
fn from_empty_interval() {
    assert_eq!(EmptiableAbsBoundPair::from(EmptyInterval), EmptiableAbsBoundPair::Empty);
}

use std::cmp::Ordering;
use std::error::Error;
use std::ops::Bound;

use jiff::Timestamp;

use super::finite_bound_position::*;
use crate::intervals::absolute::{AbsEndBound, AbsStartBound};
use crate::intervals::meta::{BoundInclusivity, HasBoundInclusivity};

#[test]
fn new() -> Result<(), Box<dyn Error>> {
    let time = "2025-01-01 00:00:00Z".parse::<Timestamp>()?;
    let abs_finite_bound_position = AbsFiniteBoundPos::new(time);

    assert_eq!(abs_finite_bound_position.time(), time);
    assert_eq!(abs_finite_bound_position.inclusivity(), BoundInclusivity::Inclusive);
    Ok(())
}

#[test]
fn new_with_inclusivity() -> Result<(), Box<dyn Error>> {
    let time = "2025-01-01 00:00:00Z".parse::<Timestamp>()?;
    let abs_finite_bound_position = AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive);

    assert_eq!(abs_finite_bound_position.time(), time);
    assert_eq!(abs_finite_bound_position.inclusivity(), BoundInclusivity::Exclusive);
    Ok(())
}

#[test]
fn time() -> Result<(), Box<dyn Error>> {
    let time = "2026-01-01 00:00:00Z".parse::<Timestamp>()?;
    let interval = AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive);

    assert_eq!(interval.time(), time);
    Ok(())
}

#[test]
fn set_time() -> Result<(), Box<dyn Error>> {
    let mut abs_finite_bound_position = AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?);
    let new_time = "2025-05-01 00:00:00Z".parse::<Timestamp>()?;

    abs_finite_bound_position.set_time(new_time);

    assert_eq!(abs_finite_bound_position.time(), new_time);
    Ok(())
}

#[test]
fn set_inclusivity() -> Result<(), Box<dyn Error>> {
    let mut abs_finite_bound_position = AbsFiniteBoundPos::new_with_incl(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    );

    abs_finite_bound_position.set_inclusivity(BoundInclusivity::Inclusive);

    assert_eq!(abs_finite_bound_position.inclusivity(), BoundInclusivity::Inclusive);
    Ok(())
}

#[test]
fn to_start_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        )
        .to_start_bound(),
        AbsStartBound::Finite(
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_finite_start_bound()
        )
    );
    Ok(())
}

#[test]
fn to_end_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        )
        .to_end_bound(),
        AbsEndBound::Finite(
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_finite_end_bound()
        )
    );
    Ok(())
}

#[test]
fn inclusivity() -> Result<(), Box<dyn Error>> {
    let inclusive = AbsFiniteBoundPos::new_with_incl(
        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Inclusive,
    );
    let exclusive = AbsFiniteBoundPos::new_with_incl(
        "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
        BoundInclusivity::Exclusive,
    );

    assert_eq!(inclusive.inclusivity(), BoundInclusivity::Inclusive);
    assert_eq!(exclusive.inclusivity(), BoundInclusivity::Exclusive);
    Ok(())
}

mod ord {
    use super::*;

    #[test]
    fn greater_times() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?)
                .cmp(&AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
            Ordering::Greater
        );
        Ok(())
    }

    #[test]
    fn less_times() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .cmp(&AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?)),
            Ordering::Less
        );
        Ok(())
    }

    #[test]
    fn equal_times_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive
            )
            .cmp(&AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive
            )),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn equal_times_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .cmp(&AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn equal_time_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .cmp(&AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )),
            Ordering::Equal
        );
        Ok(())
    }

    #[test]
    fn equal_time_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .cmp(&AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )),
            Ordering::Equal
        );
        Ok(())
    }
}

#[test]
fn from_timestamp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::from("2025-01-01 00:00:00Z".parse::<Timestamp>()?),
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        ),
    );
    Ok(())
}

#[test]
fn from_timestamp_inclusivity_pair() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::from((
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        )),
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ),
    );
    Ok(())
}

#[test]
fn try_from_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::try_from(Bound::Included("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        Ok(AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive
        )),
    );
    assert_eq!(
        AbsFiniteBoundPos::try_from(Bound::Excluded("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        Ok(AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        )),
    );
    assert_eq!(
        AbsFiniteBoundPos::try_from(Bound::Unbounded),
        Err(AbsFiniteBoundPosTryFromBoundError),
    );
    Ok(())
}

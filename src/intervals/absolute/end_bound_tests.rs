use std::cmp::Ordering;
use std::error::Error;
use std::ops::Bound;

use jiff::Timestamp;

use super::end_bound::*;
use crate::intervals::absolute::{AbsBound, AbsFiniteBoundPos, AbsStartBound};
use crate::intervals::meta::BoundInclusivity;

#[test]
fn to_bound() -> Result<(), Box<dyn Error>> {
    let end_bound = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    assert_eq!(end_bound.to_bound(), AbsBound::End(end_bound));
    Ok(())
}

#[test]
fn is_finite() -> Result<(), Box<dyn Error>> {
    assert!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .is_finite()
    );
    assert!(!AbsEndBound::InfiniteFuture.is_finite());
    Ok(())
}

#[test]
fn is_infinite_future() -> Result<(), Box<dyn Error>> {
    assert!(
        !AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .is_infinite_future()
    );
    assert!(AbsEndBound::InfiniteFuture.is_infinite_future());
    Ok(())
}

#[test]
fn finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .finite(),
        Some(AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_finite_end_bound()),
    );
    assert_eq!(AbsEndBound::InfiniteFuture.finite(), None);
    Ok(())
}

#[test]
fn opposite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .opposite(),
        Some(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
        ),
    );
    assert_eq!(AbsEndBound::InfiniteFuture.opposite(), None);
    Ok(())
}

mod ord {
    use super::*;

    #[test]
    fn inf_inf() {
        assert_eq!(
            AbsEndBound::InfiniteFuture.cmp(&AbsEndBound::InfiniteFuture),
            Ordering::Equal
        );
    }

    #[test]
    fn inf_finite() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsEndBound::InfiniteFuture
                .cmp(&AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn finite_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .to_end_bound()
                .cmp(&AbsEndBound::InfiniteFuture),
            Ordering::Less,
        );
        Ok(())
    }

    #[test]
    fn different_times_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?)
                .to_end_bound()
                .cmp(&AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn different_times_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .to_end_bound()
                .cmp(&AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
            Ordering::Less,
        );
        Ok(())
    }

    #[test]
    fn same_times_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
            .cmp(
                &AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound()
            ),
            Ordering::Equal,
        );
        Ok(())
    }

    #[test]
    fn same_times_exclusive_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
            .cmp(
                &AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound()
            ),
            Ordering::Less,
        );
        Ok(())
    }

    #[test]
    fn same_times_inclusive_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_end_bound()
            .cmp(
                &AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound()
            ),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn same_times_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_end_bound()
            .cmp(
                &AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound()
            ),
            Ordering::Equal,
        );
        Ok(())
    }
}

#[test]
fn from_absolute_finite_bound_position() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsEndBound::from(AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )),
        AbsEndBound::Finite(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_finite_end_bound()
        ),
    );
    Ok(())
}

#[test]
fn from_opt_timestamp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsEndBound::from(Some("2026-01-01 08:00:00Z".parse::<Timestamp>()?)),
        AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_end_bound()
    );
    assert_eq!(AbsEndBound::from(None::<Timestamp>), AbsEndBound::InfiniteFuture);
    Ok(())
}

#[test]
fn from_opt_timestamp_inclusivity() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsEndBound::from(Some((
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        ))),
        AbsFiniteBoundPos::new_with_incl(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        )
        .to_end_bound()
    );
    assert_eq!(
        AbsEndBound::from(None::<(Timestamp, BoundInclusivity)>),
        AbsEndBound::InfiniteFuture
    );
    Ok(())
}

#[test]
fn from_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsEndBound::from(Bound::Included("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );
    assert_eq!(
        AbsEndBound::from(Bound::Excluded("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    assert_eq!(AbsEndBound::from(Bound::Unbounded), AbsEndBound::InfiniteFuture);
    Ok(())
}

#[test]
fn try_from_abs_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsEndBound::try_from(
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_end_bound()
            .to_bound()
        ),
        Ok(AbsFiniteBoundPos::new_with_incl(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        )
        .to_end_bound())
    );
    assert_eq!(
        AbsEndBound::try_from(AbsEndBound::InfiniteFuture.to_bound()),
        Ok(AbsEndBound::InfiniteFuture)
    );

    assert_eq!(
        AbsEndBound::try_from(
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_start_bound()
            .to_bound()
        ),
        Err(AbsEndBoundTryFromAbsBoundError)
    );
    assert_eq!(
        AbsEndBound::try_from(AbsStartBound::InfinitePast.to_bound()),
        Err(AbsEndBoundTryFromAbsBoundError)
    );

    Ok(())
}

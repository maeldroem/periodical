use std::cmp::Ordering;
use std::error::Error;
use std::ops::Bound;

use jiff::Timestamp;

use super::end_bound::*;
use crate::intervals::absolute::{AbsoluteBound, AbsoluteFiniteBoundPosition, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;

#[test]
fn to_bound() -> Result<(), Box<dyn Error>> {
    let end_bound = AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    assert_eq!(end_bound.to_bound(), AbsoluteBound::End(end_bound));
    Ok(())
}

#[test]
fn is_finite() -> Result<(), Box<dyn Error>> {
    assert!(
        AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .is_finite()
    );
    assert!(!AbsoluteEndBound::InfiniteFuture.is_finite());
    Ok(())
}

#[test]
fn is_infinite_future() -> Result<(), Box<dyn Error>> {
    assert!(
        !AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .is_infinite_future()
    );
    assert!(AbsoluteEndBound::InfiniteFuture.is_infinite_future());
    Ok(())
}

#[test]
fn finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .finite(),
        Some(AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_finite_end_bound()),
    );
    assert_eq!(AbsoluteEndBound::InfiniteFuture.finite(), None);
    Ok(())
}

#[test]
fn opposite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .opposite(),
        Some(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
        ),
    );
    assert_eq!(AbsoluteEndBound::InfiniteFuture.opposite(), None);
    Ok(())
}

mod ord {
    use super::*;

    #[test]
    fn inf_inf() {
        assert_eq!(
            AbsoluteEndBound::InfiniteFuture.cmp(&AbsoluteEndBound::InfiniteFuture),
            Ordering::Equal
        );
    }

    #[test]
    fn inf_finite() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteEndBound::InfiniteFuture
                .cmp(&AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn finite_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .to_end_bound()
                .cmp(&AbsoluteEndBound::InfiniteFuture),
            Ordering::Less,
        );
        Ok(())
    }

    #[test]
    fn different_times_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?)
                .to_end_bound()
                .cmp(&AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn different_times_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .to_end_bound()
                .cmp(&AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
            Ordering::Less,
        );
        Ok(())
    }

    #[test]
    fn same_times_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
            .cmp(
                &AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
            .cmp(
                &AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_end_bound()
            .cmp(
                &AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_end_bound()
            .cmp(
                &AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
        AbsoluteEndBound::from(AbsoluteFiniteBoundPosition::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )),
        AbsoluteEndBound::Finite(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
        AbsoluteEndBound::from(Some("2026-01-01 08:00:00Z".parse::<Timestamp>()?)),
        AbsoluteFiniteBoundPosition::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_end_bound()
    );
    assert_eq!(
        AbsoluteEndBound::from(None::<Timestamp>),
        AbsoluteEndBound::InfiniteFuture
    );
    Ok(())
}

#[test]
fn from_opt_timestamp_inclusivity() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteEndBound::from(Some((
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        ))),
        AbsoluteFiniteBoundPosition::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        )
        .to_end_bound()
    );
    assert_eq!(
        AbsoluteEndBound::from(None::<(Timestamp, BoundInclusivity)>),
        AbsoluteEndBound::InfiniteFuture
    );
    Ok(())
}

#[test]
fn from_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteEndBound::from(Bound::Included("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        AbsoluteFiniteBoundPosition::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );
    assert_eq!(
        AbsoluteEndBound::from(Bound::Excluded("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        AbsoluteFiniteBoundPosition::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_end_bound(),
    );
    assert_eq!(
        AbsoluteEndBound::from(Bound::Unbounded),
        AbsoluteEndBound::InfiniteFuture
    );
    Ok(())
}

#[test]
fn try_from_abs_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteEndBound::try_from(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_end_bound()
            .to_bound()
        ),
        Ok(AbsoluteFiniteBoundPosition::new_with_inclusivity(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        )
        .to_end_bound())
    );
    assert_eq!(
        AbsoluteEndBound::try_from(AbsoluteEndBound::InfiniteFuture.to_bound()),
        Ok(AbsoluteEndBound::InfiniteFuture)
    );

    assert_eq!(
        AbsoluteEndBound::try_from(
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_start_bound()
            .to_bound()
        ),
        Err(AbsoluteEndBoundTryFromAbsoluteBoundError)
    );
    assert_eq!(
        AbsoluteEndBound::try_from(AbsoluteStartBound::InfinitePast.to_bound()),
        Err(AbsoluteEndBoundTryFromAbsoluteBoundError)
    );

    Ok(())
}

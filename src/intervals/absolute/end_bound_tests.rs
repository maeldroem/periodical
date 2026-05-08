use std::cmp::Ordering;
use std::error::Error;
use std::ops::Bound;

use jiff::Timestamp;

use super::end_bound::*;
use crate::intervals::absolute::{AbsoluteBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;

#[test]
fn to_bound() -> Result<(), Box<dyn Error>> {
    let end_bound = AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound();

    assert_eq!(end_bound.to_bound(), AbsoluteBound::End(end_bound));
    Ok(())
}

#[test]
fn is_finite() -> Result<(), Box<dyn Error>> {
    assert!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .is_finite()
    );
    assert!(!AbsoluteEndBound::InfiniteFuture.is_finite());
    Ok(())
}

#[test]
fn is_infinite_future() -> Result<(), Box<dyn Error>> {
    assert!(
        !AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .is_infinite_future()
    );
    assert!(AbsoluteEndBound::InfiniteFuture.is_infinite_future());
    Ok(())
}

#[test]
fn finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .finite(),
        Some(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
    );
    assert_eq!(AbsoluteEndBound::InfiniteFuture.finite(), None);
    Ok(())
}

#[test]
fn opposite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .opposite(),
        Some(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
        ),
    );
    assert_eq!(AbsoluteEndBound::InfiniteFuture.opposite(), None);
    Ok(())
}

mod partial_eq_start_bound {
    use super::*;

    #[test]
    fn inf_start_bound_inf() {
        assert_ne!(AbsoluteEndBound::InfiniteFuture, AbsoluteStartBound::InfinitePast);
    }

    #[test]
    fn inf_start_bound_finite() -> Result<(), Box<dyn Error>> {
        assert_ne!(
            AbsoluteEndBound::InfiniteFuture,
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        );
        Ok(())
    }

    #[test]
    fn finite_start_bound_inf() -> Result<(), Box<dyn Error>> {
        assert_ne!(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            AbsoluteStartBound::InfinitePast,
        );
        Ok(())
    }

    #[test]
    fn finite_start_bound_finite_different_times() -> Result<(), Box<dyn Error>> {
        assert_ne!(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
        );
        Ok(())
    }

    #[test]
    fn finite_start_bound_finite_equal_times_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_ne!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
        );
        Ok(())
    }

    #[test]
    fn finite_start_bound_finite_equal_times_exclusive_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_ne!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
        );
        Ok(())
    }

    #[test]
    fn finite_start_bound_finite_equal_times_inclusive_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_ne!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
        );
        Ok(())
    }

    #[test]
    fn finite_start_bound_finite_equal_times_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
        );
        Ok(())
    }
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
                .cmp(&AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn finite_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .to_end_bound()
                .cmp(&AbsoluteEndBound::InfiniteFuture),
            Ordering::Less,
        );
        Ok(())
    }

    #[test]
    fn different_times_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?)
                .to_end_bound()
                .cmp(&AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn different_times_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .to_end_bound()
                .cmp(&AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
            Ordering::Less,
        );
        Ok(())
    }

    #[test]
    fn same_times_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
            .cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
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
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
            .cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
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
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_end_bound()
            .cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
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
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_end_bound()
            .cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
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

mod partial_ord_start_bound {
    use super::*;

    #[test]
    fn inf_start_bound_inf() {
        assert_eq!(
            AbsoluteEndBound::InfiniteFuture.partial_cmp(&AbsoluteStartBound::InfinitePast),
            Some(Ordering::Greater),
        );
    }

    #[test]
    fn inf_start_bound_finite() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteEndBound::InfiniteFuture
                .partial_cmp(&AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
            Some(Ordering::Greater),
        );
        Ok(())
    }

    #[test]
    fn finite_start_bound_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .to_end_bound()
                .partial_cmp(&AbsoluteStartBound::InfinitePast),
            Some(Ordering::Greater),
        );
        Ok(())
    }

    #[test]
    fn start_bound_different_times_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?)
                .to_end_bound()
                .partial_cmp(&AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
            Some(Ordering::Greater),
        );
        Ok(())
    }

    #[test]
    fn start_bound_different_times_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .to_end_bound()
                .partial_cmp(&AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
            Some(Ordering::Less),
        );
        Ok(())
    }

    #[test]
    fn start_bound_same_times_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
            .partial_cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
            ),
            Some(Ordering::Less),
        );
        Ok(())
    }

    #[test]
    fn start_bound_same_times_exclusive_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
            .partial_cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound()
            ),
            Some(Ordering::Less),
        );
        Ok(())
    }

    #[test]
    fn start_bound_same_times_inclusive_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_end_bound()
            .partial_cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
            ),
            Some(Ordering::Less),
        );
        Ok(())
    }

    #[test]
    fn start_bound_same_times_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_end_bound()
            .partial_cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound()
            ),
            Some(Ordering::Equal),
        );
        Ok(())
    }
}

#[test]
fn from_absolute_finite_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteEndBound::from(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )),
    );
    Ok(())
}

#[test]
fn from_opt_timestamp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteEndBound::from(Some("2026-01-01 08:00:00Z".parse::<Timestamp>()?)),
        AbsoluteFiniteBound::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_end_bound()
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
        AbsoluteFiniteBound::new_with_inclusivity(
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
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_end_bound(),
    );
    assert_eq!(
        AbsoluteEndBound::from(Bound::Excluded("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        AbsoluteFiniteBound::new_with_inclusivity(
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
            AbsoluteFiniteBound::new_with_inclusivity(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_end_bound()
            .to_bound()
        ),
        Ok(AbsoluteFiniteBound::new_with_inclusivity(
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
            AbsoluteFiniteBound::new_with_inclusivity(
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

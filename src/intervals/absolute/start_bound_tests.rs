use std::cmp::Ordering;
use std::error::Error;
use std::ops::Bound;

use jiff::Timestamp;

use super::start_bound::*;
use crate::intervals::absolute::{AbsoluteBound, AbsoluteEndBound, AbsoluteFiniteBound};
use crate::intervals::meta::BoundInclusivity;

#[test]
fn to_bound() -> Result<(), Box<dyn Error>> {
    let start_bound = AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();

    assert_eq!(start_bound.to_bound(), AbsoluteBound::Start(start_bound),);
    Ok(())
}

#[test]
fn is_finite() -> Result<(), Box<dyn Error>> {
    assert!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .is_finite()
    );
    assert!(!AbsoluteStartBound::InfinitePast.is_finite());
    Ok(())
}

#[test]
fn is_infinite_past() -> Result<(), Box<dyn Error>> {
    assert!(
        !AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .is_infinite_past()
    );
    assert!(AbsoluteStartBound::InfinitePast.is_infinite_past());
    Ok(())
}

#[test]
fn finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .finite(),
        Some(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
    );
    assert_eq!(AbsoluteStartBound::InfinitePast.finite(), None);
    Ok(())
}

#[test]
fn opposite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .opposite(),
        Some(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
        ),
    );
    assert_eq!(AbsoluteStartBound::InfinitePast.opposite(), None);
    Ok(())
}

mod partial_eq_end_bound {
    use super::*;

    #[test]
    fn inf_end_bound_inf() {
        assert_ne!(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
    }

    #[test]
    fn inf_end_bound_finite() -> Result<(), Box<dyn Error>> {
        assert_ne!(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        Ok(())
    }

    #[test]
    fn finite_end_bound_inf() -> Result<(), Box<dyn Error>> {
        assert_ne!(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        );
        Ok(())
    }

    #[test]
    fn finite_end_bound_finite_different_times() -> Result<(), Box<dyn Error>> {
        assert_ne!(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        );
        Ok(())
    }

    #[test]
    fn finite_end_bound_finite_equal_times_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_ne!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        );
        Ok(())
    }

    #[test]
    fn finite_end_bound_finite_equal_times_exclusive_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_ne!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        );
        Ok(())
    }

    #[test]
    fn finite_end_bound_finite_equal_times_inclusive_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_ne!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound(),
        );
        Ok(())
    }

    #[test]
    fn finite_end_bound_finite_equal_times_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound(),
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_end_bound(),
        );
        Ok(())
    }
}

mod ord {
    use super::*;

    #[test]
    fn inf_inf() {
        assert_eq!(
            AbsoluteStartBound::InfinitePast.cmp(&AbsoluteStartBound::InfinitePast),
            Ordering::Equal
        );
    }

    #[test]
    fn inf_finite() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteStartBound::InfinitePast
                .cmp(&AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
            Ordering::Less,
        );
        Ok(())
    }

    #[test]
    fn finite_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .to_start_bound()
                .cmp(&AbsoluteStartBound::InfinitePast),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn different_times_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?)
                .to_start_bound()
                .cmp(&AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn different_times_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .to_start_bound()
                .cmp(&AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
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
            .to_start_bound()
            .cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
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
            .to_start_bound()
            .cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound()
            ),
            Ordering::Greater,
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
            .to_start_bound()
            .cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
            ),
            Ordering::Less,
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
            .to_start_bound()
            .cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound()
            ),
            Ordering::Equal,
        );
        Ok(())
    }
}

mod partial_ord_end_bound {
    use super::*;

    #[test]
    fn inf_end_bound_inf() {
        assert_eq!(
            AbsoluteStartBound::InfinitePast.partial_cmp(&AbsoluteEndBound::InfiniteFuture),
            Some(Ordering::Less),
        );
    }

    #[test]
    fn inf_end_bound_finite() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteStartBound::InfinitePast
                .partial_cmp(&AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
            Some(Ordering::Less),
        );
        Ok(())
    }

    #[test]
    fn finite_end_bound_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .to_start_bound()
                .partial_cmp(&AbsoluteEndBound::InfiniteFuture),
            Some(Ordering::Less),
        );
        Ok(())
    }

    #[test]
    fn end_bound_different_times_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?)
                .to_start_bound()
                .partial_cmp(&AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
            Some(Ordering::Greater),
        );
        Ok(())
    }

    #[test]
    fn end_bound_different_times_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .to_start_bound()
                .partial_cmp(&AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
            Some(Ordering::Less),
        );
        Ok(())
    }

    #[test]
    fn end_bound_same_times_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
            .partial_cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound()
            ),
            Some(Ordering::Greater),
        );
        Ok(())
    }

    #[test]
    fn end_bound_same_times_exclusive_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
            .partial_cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound()
            ),
            Some(Ordering::Greater),
        );
        Ok(())
    }

    #[test]
    fn end_bound_same_times_inclusive_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound()
            .partial_cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound()
            ),
            Some(Ordering::Greater),
        );
        Ok(())
    }

    #[test]
    fn end_bound_same_times_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound()
            .partial_cmp(
                &AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound()
            ),
            Some(Ordering::Equal),
        );
        Ok(())
    }
}

#[test]
fn from_absolute_finite_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteStartBound::from(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )),
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )),
    );
    Ok(())
}

#[test]
fn from_opt_timestamp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteStartBound::from(Some("2026-01-01 08:00:00Z".parse::<Timestamp>()?)),
        AbsoluteFiniteBound::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound()
    );
    assert_eq!(
        AbsoluteStartBound::from(None::<Timestamp>),
        AbsoluteStartBound::InfinitePast
    );
    Ok(())
}

#[test]
fn from_opt_timestamp_inclusivity() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteStartBound::from(Some((
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        ))),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        )
        .to_start_bound()
    );
    assert_eq!(
        AbsoluteStartBound::from(None::<(Timestamp, BoundInclusivity)>),
        AbsoluteStartBound::InfinitePast
    );
    Ok(())
}

#[test]
fn from_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteStartBound::from(Bound::Included("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        AbsoluteStartBound::from(Bound::Excluded("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        AbsoluteStartBound::from(Bound::Unbounded),
        AbsoluteStartBound::InfinitePast
    );

    Ok(())
}

#[test]
fn try_from_abs_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteStartBound::try_from(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_start_bound()
            .to_bound()
        ),
        Ok(AbsoluteFiniteBound::new_with_inclusivity(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        )
        .to_start_bound())
    );
    assert_eq!(
        AbsoluteStartBound::try_from(AbsoluteStartBound::InfinitePast.to_bound()),
        Ok(AbsoluteStartBound::InfinitePast)
    );

    assert_eq!(
        AbsoluteStartBound::try_from(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_end_bound()
            .to_bound()
        ),
        Err(AbsoluteStartBoundTryFromAbsoluteBoundError)
    );
    assert_eq!(
        AbsoluteStartBound::try_from(AbsoluteEndBound::InfiniteFuture.to_bound()),
        Err(AbsoluteStartBoundTryFromAbsoluteBoundError)
    );

    Ok(())
}

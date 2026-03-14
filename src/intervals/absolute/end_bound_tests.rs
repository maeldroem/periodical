use std::cmp::Ordering;
use std::error::Error;
use std::ops::Bound;

use jiff::Timestamp;

use crate::intervals::absolute::{AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;

use super::end_bound::*;


#[test]
fn is_finite() -> Result<(), Box<dyn Error>> {
    assert!(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound().is_finite());
    assert!(!AbsoluteEndBound::InfiniteFuture.is_finite());
    Ok(())
}

#[test]
fn is_infinite_future() -> Result<(), Box<dyn Error>> {
    assert!(
        !AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound().is_infinite_future()
    );
    assert!(AbsoluteEndBound::InfiniteFuture.is_infinite_future());
    Ok(())
}

#[test]
fn finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound().finite(),
        Some(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
    );
    assert_eq!(AbsoluteEndBound::InfiniteFuture.finite(), None);
    Ok(())
}

#[test]
fn opposite_finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound().opposite(),
        Some(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ).to_start_bound()),
    );
    Ok(())
}

#[test]
fn opposite_infinite_past() {
    assert_eq!(AbsoluteEndBound::InfiniteFuture.opposite(), None);
}

#[test]
fn inf_absolute_start_bound_inf_eq() {
    assert_ne!(AbsoluteEndBound::InfiniteFuture, AbsoluteStartBound::InfinitePast);
}

#[test]
fn inf_absolute_start_bound_finite_eq() -> Result<(), Box<dyn Error>> {
    assert_ne!(
        AbsoluteEndBound::InfiniteFuture,
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    );
    Ok(())
}

#[test]
fn finite_absolute_start_bound_inf_eq() -> Result<(), Box<dyn Error>> {
    assert_ne!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        AbsoluteStartBound::InfinitePast,
    );
    Ok(())
}

#[test]
fn finite_absolute_start_bound_finite_different_times_eq() -> Result<(), Box<dyn Error>> {
    assert_ne!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
    );
    Ok(())
}

#[test]
fn finite_absolute_start_bound_finite_equal_times_exclusive_bounds_eq() -> Result<(), Box<dyn Error>> {
    assert_ne!(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ).to_end_bound(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ).to_start_bound(),
    );
    Ok(())
}

#[test]
fn finite_absolute_start_bound_finite_equal_times_exclusive_inclusive_bounds_eq() -> Result<(), Box<dyn Error>> {
    assert_ne!(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ).to_end_bound(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        ).to_start_bound(),
    );
    Ok(())
}

#[test]
fn finite_absolute_start_bound_finite_equal_times_inclusive_exclusive_bounds_eq() -> Result<(), Box<dyn Error>> {
    assert_ne!(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        ).to_end_bound(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ).to_start_bound(),
    );
    Ok(())
}

#[test]
fn finite_absolute_start_bound_finite_equal_times_inclusive_bounds_eq() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        ).to_end_bound(),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        ).to_start_bound(),
    );
    Ok(())
}

#[test]
fn inf_inf_cmp() {
    assert_eq!(
        AbsoluteEndBound::InfiniteFuture.cmp(&AbsoluteEndBound::InfiniteFuture),
        Ordering::Equal
    );
}

#[test]
fn inf_finite_cmp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteEndBound::InfiniteFuture
            .cmp(&AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
        Ordering::Greater,
    );
    Ok(())
}

#[test]
fn finite_inf_cmp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .cmp(&AbsoluteEndBound::InfiniteFuture),
        Ordering::Less,
    );
    Ok(())
}

#[test]
fn different_times_cmp_greater() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .cmp(&AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
        Ordering::Greater,
    );
    Ok(())
}

#[test]
fn different_times_cmp_less() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .cmp(&AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
        Ordering::Less,
    );
    Ok(())
}

#[test]
fn same_times_exclusive_bounds_cmp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
            .to_end_bound()
            .cmp(&AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            ).to_end_bound()),
        Ordering::Equal,
    );
    Ok(())
}

#[test]
fn same_times_exclusive_inclusive_bounds_cmp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
            .to_end_bound()
            .cmp(&AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            ).to_end_bound()),
        Ordering::Less,
    );
    Ok(())
}

#[test]
fn same_times_inclusive_exclusive_bounds_cmp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
            .to_end_bound()
            .cmp(&AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            ).to_end_bound()),
        Ordering::Greater,
    );
    Ok(())
}

#[test]
fn same_times_inclusive_bounds_cmp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
            .to_end_bound()
            .cmp(&AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            ).to_end_bound()),
        Ordering::Equal,
    );
    Ok(())
}

#[test]
fn inf_absolute_start_bound_inf_partial_cmp() {
    assert_eq!(
        AbsoluteEndBound::InfiniteFuture.partial_cmp(&AbsoluteStartBound::InfinitePast),
        Some(Ordering::Greater),
    );
}

#[test]
fn inf_absolute_start_bound_finite_partial_cmp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteEndBound::InfiniteFuture
            .partial_cmp(&AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
        Some(Ordering::Greater),
    );
    Ok(())
}

#[test]
fn finite_absolute_start_bound_inf_partial_cmp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .partial_cmp(&AbsoluteStartBound::InfinitePast),
        Some(Ordering::Greater),
    );
    Ok(())
}

#[test]
fn absolute_start_bound_different_times_partial_cmp_greater() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .partial_cmp(
                &AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()
            ),
        Some(Ordering::Greater),
    );
    Ok(())
}

#[test]
fn absolute_start_bound_different_times_partial_cmp_less() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .partial_cmp(
                &AbsoluteFiniteBound::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound()
            ),
        Some(Ordering::Less),
    );
    Ok(())
}

#[test]
fn absolute_start_bound_same_times_exclusive_bounds_partial_cmp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
            .to_end_bound()
            .partial_cmp(&AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            ).to_start_bound()),
        Some(Ordering::Less),
    );
    Ok(())
}

#[test]
fn absolute_start_bound_same_times_exclusive_inclusive_bounds_partial_cmp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
            .to_end_bound()
            .partial_cmp(&AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            ).to_start_bound()),
        Some(Ordering::Less),
    );
    Ok(())
}

#[test]
fn absolute_start_bound_same_times_inclusive_exclusive_bounds_partial_cmp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
            .to_end_bound()
            .partial_cmp(&AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            ).to_start_bound()),
        Some(Ordering::Less),
    );
    Ok(())
}

#[test]
fn absolute_start_bound_same_times_inclusive_bounds_partial_cmp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
            .to_end_bound()
            .partial_cmp(&AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            ).to_start_bound()),
        Some(Ordering::Equal),
    );
    Ok(())
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
fn from_inclusive_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteEndBound::from(Bound::Included("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        ).to_end_bound(),
    );
    Ok(())
}

#[test]
fn from_exclusive_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteEndBound::from(Bound::Excluded("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ).to_end_bound(),
    );
    Ok(())
}

#[test]
fn from_unbounded_bound() {
    assert_eq!(
        AbsoluteEndBound::from(Bound::Unbounded),
        AbsoluteEndBound::InfiniteFuture
    );
}

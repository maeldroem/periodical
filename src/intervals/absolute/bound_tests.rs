use std::error::Error;
use std::hash::{DefaultHasher, Hash, Hasher};

use jiff::Timestamp;

use super::bound::*;
use crate::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;

#[test]
fn is_start() {
    assert!(AbsoluteStartBound::InfinitePast.to_bound().is_start());
    assert!(!AbsoluteEndBound::InfiniteFuture.to_bound().is_start());
}

#[test]
fn is_end() {
    assert!(!AbsoluteStartBound::InfinitePast.to_bound().is_end());
    assert!(AbsoluteEndBound::InfiniteFuture.to_bound().is_end());
}

#[test]
fn start() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
            .start(),
        Some(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
    );
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
            .start(),
        None,
    );
    Ok(())
}

#[test]
fn end() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
            .end(),
        None,
    );
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
            .end(),
        Some(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
    );
    Ok(())
}

#[test]
fn start_inf_past_opposite() {
    assert_eq!(AbsoluteStartBound::InfinitePast.to_bound().opposite(), None);
}

#[test]
fn start_finite_opposite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
            .opposite(),
        Some(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
            .to_bound()
        ),
    );
    Ok(())
}

#[test]
fn end_inf_future_opposite() {
    assert_eq!(AbsoluteEndBound::InfiniteFuture.to_bound().opposite(), None);
}

#[test]
fn end_finite_opposite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
            .opposite(),
        Some(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
            .to_bound()
        ),
    );
    Ok(())
}

#[test]
fn equality() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound(),
        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
    );
    assert_eq!(
        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound(),
        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
    );
    assert_eq!(
        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound(),
        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
    );
    assert_eq!(
        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound(),
        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
    );

    Ok(())
}

#[test]
fn hash_infinite_past() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    AbsoluteStartBound::InfinitePast.to_bound().hash(&mut hasher1);
    AbsoluteStartBound::InfinitePast.to_bound().hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());
}

#[test]
fn hash_infinite_future() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    AbsoluteEndBound::InfiniteFuture.to_bound().hash(&mut hasher1);
    AbsoluteEndBound::InfiniteFuture.to_bound().hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());
}

#[test]
fn hash_finite_start() -> Result<(), Box<dyn Error>> {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());

    Ok(())
}

#[test]
fn hash_finite_end() -> Result<(), Box<dyn Error>> {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher1);
    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher2);

    Ok(())
}

#[test]
fn hash_finite_start_end() -> Result<(), Box<dyn Error>> {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());

    Ok(())
}

#[test]
fn hash_finite_start_end_no_match() -> Result<(), Box<dyn Error>> {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    AbsoluteFiniteBound::new("2026-01-01 00:00:01Z".parse::<Timestamp>()?)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher2);

    assert_ne!(hasher1.finish(), hasher2.finish());

    Ok(())
}

#[test]
fn from_absolute_start_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBound::from(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
        AbsoluteBound::Start(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
    );
    Ok(())
}

#[test]
fn from_absolute_end_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBound::from(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
        AbsoluteBound::End(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
    );
    Ok(())
}

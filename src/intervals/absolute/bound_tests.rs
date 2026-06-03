use std::error::Error;
use std::hash::{DefaultHasher, Hash, Hasher};

use jiff::Timestamp;

use super::bound::*;
use crate::intervals::absolute::{AbsEndBound, AbsFiniteBoundPos, AbsStartBound};
use crate::intervals::meta::BoundInclusivity;

#[test]
fn is_start() {
    assert!(AbsStartBound::InfinitePast.to_bound().is_start());
    assert!(!AbsEndBound::InfiniteFuture.to_bound().is_start());
}

#[test]
fn is_end() {
    assert!(!AbsStartBound::InfinitePast.to_bound().is_end());
    assert!(AbsEndBound::InfiniteFuture.to_bound().is_end());
}

#[test]
fn start() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
            .start(),
        Some(AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
    );
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
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
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
            .end(),
        None,
    );
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
            .end(),
        Some(AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
    );
    Ok(())
}

#[test]
fn start_inf_past_opposite() {
    assert_eq!(AbsStartBound::InfinitePast.to_bound().opposite(), None);
}

#[test]
fn start_finite_opposite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
            .opposite(),
        Some(
            AbsFiniteBoundPos::new_with_incl(
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
    assert_eq!(AbsEndBound::InfiniteFuture.to_bound().opposite(), None);
}

#[test]
fn end_finite_opposite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
            .opposite(),
        Some(
            AbsFiniteBoundPos::new_with_incl(
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
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound(),
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
    );
    assert_eq!(
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound(),
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
    );
    assert_eq!(
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound(),
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
    );
    assert_eq!(
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound(),
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
    );

    Ok(())
}

#[test]
fn hash_infinite_past() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    AbsStartBound::InfinitePast.to_bound().hash(&mut hasher1);
    AbsStartBound::InfinitePast.to_bound().hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());
}

#[test]
fn hash_infinite_future() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    AbsEndBound::InfiniteFuture.to_bound().hash(&mut hasher1);
    AbsEndBound::InfiniteFuture.to_bound().hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());
}

#[test]
fn hash_finite_start() -> Result<(), Box<dyn Error>> {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
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

    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher1);
    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher2);

    Ok(())
}

#[test]
fn hash_finite_start_end() -> Result<(), Box<dyn Error>> {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
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

    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    AbsFiniteBoundPos::new("2026-01-01 00:00:01Z".parse::<Timestamp>()?)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher2);

    assert_ne!(hasher1.finish(), hasher2.finish());

    Ok(())
}

#[test]
fn from_absolute_start_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBound::from(AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
        AbsBound::Start(AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
    );
    Ok(())
}

#[test]
fn from_absolute_end_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBound::from(AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
        AbsBound::End(AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
    );
    Ok(())
}

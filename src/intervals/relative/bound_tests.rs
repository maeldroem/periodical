use std::error::Error;
use std::hash::{DefaultHasher, Hash, Hasher};

use jiff::SignedDuration;

use super::bound::*;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeEndBound, RelativeFiniteBound, RelativeStartBound};

#[test]
fn is_start() {
    assert!(RelativeStartBound::InfinitePast.to_bound().is_start());
    assert!(!RelativeEndBound::InfiniteFuture.to_bound().is_start());
}

#[test]
fn is_end() {
    assert!(!RelativeStartBound::InfinitePast.to_bound().is_end());
    assert!(RelativeEndBound::InfiniteFuture.to_bound().is_end());
}

#[test]
fn start() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound()
            .start(),
        Some(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()),
    );
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
            .start(),
        None,
    );
}

#[test]
fn end() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound()
            .end(),
        None,
    );
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
            .end(),
        Some(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()),
    );
}

#[test]
fn start_inf_past_opposite() {
    assert_eq!(RelativeStartBound::InfinitePast.to_bound().opposite(), None);
}

#[test]
fn start_finite_opposite() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound()
            .opposite(),
        Some(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_end_bound()
                .to_bound()
        ),
    );
}

#[test]
fn end_inf_future_opposite() {
    assert_eq!(RelativeEndBound::InfiniteFuture.to_bound().opposite(), None);
}

#[test]
fn end_finite_opposite() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
            .opposite(),
        Some(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_start_bound()
                .to_bound()
        ),
    );
}

#[test]
fn equality() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound(),
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound()
    );
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound(),
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
    );
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound(),
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
    );
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound(),
        RelativeFiniteBound::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
    );
}

#[test]
fn hash_infinite_past() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    RelativeStartBound::InfinitePast.to_bound().hash(&mut hasher1);
    RelativeStartBound::InfinitePast.to_bound().hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());
}

#[test]
fn hash_infinite_future() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    RelativeEndBound::InfiniteFuture.to_bound().hash(&mut hasher1);
    RelativeEndBound::InfiniteFuture.to_bound().hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());
}

#[test]
fn hash_finite_start() -> Result<(), Box<dyn Error>> {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    RelativeFiniteBound::new(SignedDuration::ZERO)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    RelativeFiniteBound::new(SignedDuration::ZERO)
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

    RelativeFiniteBound::new(SignedDuration::ZERO)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher1);
    RelativeFiniteBound::new(SignedDuration::ZERO)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher2);

    Ok(())
}

#[test]
fn hash_finite_start_end() -> Result<(), Box<dyn Error>> {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    RelativeFiniteBound::new(SignedDuration::ZERO)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    RelativeFiniteBound::new(SignedDuration::ZERO)
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

    RelativeFiniteBound::new(SignedDuration::ZERO)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    RelativeFiniteBound::new(SignedDuration::from_secs(1))
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher2);

    assert_ne!(hasher1.finish(), hasher2.finish());

    Ok(())
}

#[test]
fn from_relative_start_bound() {
    assert_eq!(
        RelativeBound::from(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()),
        RelativeBound::Start(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()),
    );
}

#[test]
fn from_relative_end_bound() {
    assert_eq!(
        RelativeBound::from(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()),
        RelativeBound::End(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()),
    );
}

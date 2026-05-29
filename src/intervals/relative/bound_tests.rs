use std::hash::{DefaultHasher, Hash, Hasher};

use jiff::SignedDuration;

use super::bound::*;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeEndBound, RelativeFiniteBoundPosition, RelativeStartBound};

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
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound()
            .start(),
        Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound()),
    );
    assert_eq!(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
            .start(),
        None,
    );
}

#[test]
fn end() {
    assert_eq!(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound()
            .end(),
        None,
    );
    assert_eq!(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
            .end(),
        Some(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound()),
    );
}

#[test]
fn start_inf_past_opposite() {
    assert_eq!(RelativeStartBound::InfinitePast.to_bound().opposite(), None);
}

#[test]
fn start_finite_opposite() {
    assert_eq!(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound()
            .opposite(),
        Some(
            RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
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
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
            .opposite(),
        Some(
            RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_start_bound()
                .to_bound()
        ),
    );
}

#[test]
fn equality() {
    assert_eq!(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound(),
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound()
    );
    assert_eq!(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound(),
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
    );
    assert_eq!(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound(),
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
    );
    assert_eq!(
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound(),
        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
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
fn hash_finite_start() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    RelativeFiniteBoundPosition::new(SignedDuration::ZERO)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    RelativeFiniteBoundPosition::new(SignedDuration::ZERO)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());
}

#[test]
fn hash_finite_end() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    RelativeFiniteBoundPosition::new(SignedDuration::ZERO)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher1);
    RelativeFiniteBoundPosition::new(SignedDuration::ZERO)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher2);
}

#[test]
fn hash_finite_start_end() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    RelativeFiniteBoundPosition::new(SignedDuration::ZERO)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    RelativeFiniteBoundPosition::new(SignedDuration::ZERO)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());
}

#[test]
fn hash_finite_start_end_no_match() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    RelativeFiniteBoundPosition::new(SignedDuration::ZERO)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    RelativeFiniteBoundPosition::new(SignedDuration::from_secs(1))
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher2);

    assert_ne!(hasher1.finish(), hasher2.finish());
}

#[test]
fn from_relative_start_bound() {
    assert_eq!(
        RelativeBound::from(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound()),
        RelativeBound::Start(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound()),
    );
}

#[test]
fn from_relative_end_bound() {
    assert_eq!(
        RelativeBound::from(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound()),
        RelativeBound::End(RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound()),
    );
}

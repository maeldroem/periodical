use std::hash::{DefaultHasher, Hash, Hasher};

use jiff::SignedDuration;

use super::bound::*;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelStartBound, RelEndBound, RelFiniteBoundPos};

#[test]
fn is_start() {
    assert!(RelStartBound::InfinitePast.to_bound().is_start());
    assert!(!RelEndBound::InfiniteFuture.to_bound().is_start());
}

#[test]
fn is_end() {
    assert!(!RelStartBound::InfinitePast.to_bound().is_end());
    assert!(RelEndBound::InfiniteFuture.to_bound().is_end());
}

#[test]
fn start() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound()
            .start(),
        Some(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()),
    );
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
            .start(),
        None,
    );
}

#[test]
fn end() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound()
            .end(),
        None,
    );
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
            .end(),
        Some(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()),
    );
}

#[test]
fn start_inf_past_opposite() {
    assert_eq!(RelStartBound::InfinitePast.to_bound().opposite(), None);
}

#[test]
fn start_finite_opposite() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound()
            .opposite(),
        Some(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_end_bound()
                .to_bound()
        ),
    );
}

#[test]
fn end_inf_future_opposite() {
    assert_eq!(RelEndBound::InfiniteFuture.to_bound().opposite(), None);
}

#[test]
fn end_finite_opposite() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
            .opposite(),
        Some(
            RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_start_bound()
                .to_bound()
        ),
    );
}

#[test]
fn equality() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound()
    );
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
    );
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
    );
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_start_bound()
            .to_bound(),
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_end_bound()
            .to_bound()
    );
}

#[test]
fn hash_infinite_past() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    RelStartBound::InfinitePast.to_bound().hash(&mut hasher1);
    RelStartBound::InfinitePast.to_bound().hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());
}

#[test]
fn hash_infinite_future() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    RelEndBound::InfiniteFuture.to_bound().hash(&mut hasher1);
    RelEndBound::InfiniteFuture.to_bound().hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());
}

#[test]
fn hash_finite_start() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    RelFiniteBoundPos::new(SignedDuration::ZERO)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    RelFiniteBoundPos::new(SignedDuration::ZERO)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());
}

#[test]
fn hash_finite_end() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    RelFiniteBoundPos::new(SignedDuration::ZERO)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher1);
    RelFiniteBoundPos::new(SignedDuration::ZERO)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher2);
}

#[test]
fn hash_finite_start_end() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    RelFiniteBoundPos::new(SignedDuration::ZERO)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    RelFiniteBoundPos::new(SignedDuration::ZERO)
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher2);

    assert_eq!(hasher1.finish(), hasher2.finish());
}

#[test]
fn hash_finite_start_end_no_match() {
    let mut hasher1 = DefaultHasher::new();
    let mut hasher2 = DefaultHasher::new();

    RelFiniteBoundPos::new(SignedDuration::ZERO)
        .to_start_bound()
        .to_bound()
        .hash(&mut hasher1);
    RelFiniteBoundPos::new(SignedDuration::from_secs(1))
        .to_end_bound()
        .to_bound()
        .hash(&mut hasher2);

    assert_ne!(hasher1.finish(), hasher2.finish());
}

#[test]
fn from_relative_start_bound() {
    assert_eq!(
        RelBound::from(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()),
        RelBound::Start(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound()),
    );
}

#[test]
fn from_relative_end_bound() {
    assert_eq!(
        RelBound::from(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()),
        RelBound::End(RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound()),
    );
}

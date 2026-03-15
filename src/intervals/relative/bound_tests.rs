use jiff::SignedDuration;

use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeEndBound, RelativeFiniteBound, RelativeStartBound};

use super::bound::*;

#[test]
fn relative_bound_is_start() {
    assert!(RelativeStartBound::InfinitePast.to_bound().is_start());
    assert!(!RelativeEndBound::InfiniteFuture.to_bound().is_start());
}

#[test]
fn relative_bound_is_end() {
    assert!(!RelativeStartBound::InfinitePast.to_bound().is_end());
    assert!(RelativeEndBound::InfiniteFuture.to_bound().is_end());
}

#[test]
fn relative_bound_start() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound().to_bound().start(),
        Some(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()),
    );
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound().to_bound().start(),
        None,
    );
}

#[test]
fn relative_bound_end() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound().to_bound().end(),
        None,
    );
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound().to_bound().end(),
        Some(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()),
    );
}

#[test]
fn relative_bound_start_inf_past_opposite() {
    assert_eq!(RelativeStartBound::InfinitePast.to_bound().opposite(), None);
}

#[test]
fn relative_bound_start_finite_opposite() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound().to_bound().opposite(),
        Some(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ).to_end_bound().to_bound()),
    );
}

#[test]
fn relative_bound_end_inf_future_opposite() {
    assert_eq!(RelativeEndBound::InfiniteFuture.to_bound().opposite(), None);
}

#[test]
fn relative_bound_end_finite_opposite() {
    assert_eq!(
        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound().to_bound().opposite(),
        Some(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ).to_start_bound().to_bound()),
    );
}

#[test]
fn relative_bound_from_relative_start_bound() {
    assert_eq!(
        RelativeBound::from(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()),
        RelativeBound::Start(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound()),
    );
}

#[test]
fn relative_bound_from_relative_end_bound() {
    assert_eq!(
        RelativeBound::from(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()),
        RelativeBound::End(RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()),
    );
}

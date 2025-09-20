use super::meta::*;

#[test]
fn opening_direction_from_bool() {
    assert_eq!(OpeningDirection::from(true), OpeningDirection::ToFuture);
    assert_eq!(OpeningDirection::from(false), OpeningDirection::ToPast);
}

#[test]
fn interval_duration_from_duration() {
    assert_eq!(
        Duration::from(chrono::Duration::zero()),
        Duration::Finite(chrono::Duration::zero())
    );
}

#[test]
fn bound_inclusivity_default() {
    assert_eq!(BoundInclusivity::default(), BoundInclusivity::Inclusive);
}

#[test]
fn bound_inclusive_from_bool() {
    assert_eq!(BoundInclusivity::from(true), BoundInclusivity::Inclusive);
    assert_eq!(BoundInclusivity::from(false), BoundInclusivity::Exclusive);
}

use jiff::SignedDuration;

use super::finite_bound::*;
use crate::intervals::meta::{BoundExtremality, BoundInclusivity, HasBoundExtremality};
use crate::intervals::relative::{RelBound, RelFiniteBoundPos};

#[test]
fn is_start() {
    assert!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_finite_start_bound()
            .to_finite_bound()
            .is_start()
    );
    assert!(
        !RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_finite_end_bound()
            .to_finite_bound()
            .is_start()
    );
}

#[test]
fn is_end() {
    assert!(
        !RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_finite_start_bound()
            .to_finite_bound()
            .is_end()
    );
    assert!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(1))
            .to_finite_end_bound()
            .to_finite_bound()
            .is_end()
    );
}

#[test]
fn start() {
    let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));

    assert_eq!(
        pos.to_finite_start_bound().to_finite_bound().start(),
        Some(pos.to_finite_start_bound())
    );
    assert_eq!(pos.to_finite_end_bound().to_finite_bound().start(), None);
}

#[test]
fn end() {
    let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));

    assert_eq!(pos.to_finite_start_bound().to_finite_bound().end(), None);
    assert_eq!(
        pos.to_finite_end_bound().to_finite_bound().end(),
        Some(pos.to_finite_end_bound())
    );
}

#[test]
fn pos() {
    let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));

    assert_eq!(pos.to_finite_start_bound().to_finite_bound().pos(), pos);
    assert_eq!(pos.to_finite_end_bound().to_finite_bound().pos(), pos);
}

#[test]
fn opposite() {
    let time = SignedDuration::from_hours(1);
    let pos = RelFiniteBoundPos::new(time);

    assert_eq!(
        pos.to_finite_start_bound().to_finite_bound().opposite(),
        RelFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive)
            .to_finite_end_bound()
            .to_finite_bound()
    );
    assert_eq!(
        pos.to_finite_end_bound().to_finite_bound().opposite(),
        RelFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive)
            .to_finite_start_bound()
            .to_finite_bound()
    );
}

#[test]
fn to_bound() {
    let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));

    assert_eq!(
        pos.to_finite_start_bound().to_finite_bound().to_bound(),
        RelBound::Start(pos.to_finite_start_bound().to_start_bound())
    );
    assert_eq!(
        pos.to_finite_end_bound().to_finite_bound().to_bound(),
        RelBound::End(pos.to_finite_end_bound().to_end_bound())
    );
}

#[test]
fn bound_extremality() {
    let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));

    assert_eq!(
        pos.to_finite_start_bound().to_finite_bound().bound_extremality(),
        BoundExtremality::Start,
    );
    assert_eq!(
        pos.to_finite_end_bound().to_finite_bound().bound_extremality(),
        BoundExtremality::End,
    );
}

#[test]
fn from_finite_start_bound() {
    let finite_start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();

    assert_eq!(RelFiniteBound::from(finite_start), RelFiniteBound::Start(finite_start));
}

#[test]
fn from_finite_end_bound() {
    let finite_end = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound();

    assert_eq!(RelFiniteBound::from(finite_end), RelFiniteBound::End(finite_end));
}

#[test]
fn from_finite_bound_pos_and_bound_extremality() {
    let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));

    assert_eq!(
        RelFiniteBound::from((pos, BoundExtremality::Start)),
        pos.to_finite_start_bound().to_finite_bound()
    );
    assert_eq!(
        RelFiniteBound::from((pos, BoundExtremality::End)),
        pos.to_finite_end_bound().to_finite_bound()
    );
}

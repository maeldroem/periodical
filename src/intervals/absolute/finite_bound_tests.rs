use super::finite_bound::*;
use crate::intervals::absolute::{AbsBound, AbsFiniteBoundPos};
use crate::intervals::meta::{BoundExtremality, BoundInclusivity, HasBoundExtremality};
use crate::test_data::date_timestamp;

#[test]
fn is_start() {
    assert!(
        AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1))
            .to_finite_start_bound()
            .to_finite_bound()
            .is_start()
    );
    assert!(
        !AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1))
            .to_finite_end_bound()
            .to_finite_bound()
            .is_start()
    );
}

#[test]
fn is_end() {
    assert!(
        !AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1))
            .to_finite_start_bound()
            .to_finite_bound()
            .is_end()
    );
    assert!(
        AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1))
            .to_finite_end_bound()
            .to_finite_bound()
            .is_end()
    );
}

#[test]
fn start() {
    let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));

    assert_eq!(
        pos.to_finite_start_bound().to_finite_bound().start(),
        Some(pos.to_finite_start_bound())
    );
    assert_eq!(pos.to_finite_end_bound().to_finite_bound().start(), None);
}

#[test]
fn end() {
    let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));

    assert_eq!(pos.to_finite_start_bound().to_finite_bound().end(), None);
    assert_eq!(
        pos.to_finite_end_bound().to_finite_bound().end(),
        Some(pos.to_finite_end_bound())
    );
}

#[test]
fn pos() {
    let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));

    assert_eq!(pos.to_finite_start_bound().to_finite_bound().pos(), pos);
    assert_eq!(pos.to_finite_end_bound().to_finite_bound().pos(), pos);
}

#[test]
fn opposite() {
    let time = date_timestamp(2026, 1, 1);
    let pos = AbsFiniteBoundPos::new(time);

    assert_eq!(
        pos.to_finite_start_bound().to_finite_bound().opposite(),
        AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive)
            .to_finite_end_bound()
            .to_finite_bound()
    );
    assert_eq!(
        pos.to_finite_end_bound().to_finite_bound().opposite(),
        AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive)
            .to_finite_start_bound()
            .to_finite_bound()
    );
}

#[test]
fn to_bound() {
    let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));

    assert_eq!(
        pos.to_finite_start_bound().to_finite_bound().to_bound(),
        AbsBound::Start(pos.to_finite_start_bound().to_start_bound())
    );
    assert_eq!(
        pos.to_finite_end_bound().to_finite_bound().to_bound(),
        AbsBound::End(pos.to_finite_end_bound().to_end_bound())
    );
}

#[test]
fn bound_extremality() {
    let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));

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
    let finite_start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();

    assert_eq!(AbsFiniteBound::from(finite_start), AbsFiniteBound::Start(finite_start));
}

#[test]
fn from_finite_end_bound() {
    let finite_end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();

    assert_eq!(AbsFiniteBound::from(finite_end), AbsFiniteBound::End(finite_end));
}

#[test]
fn from_finite_bound_pos_and_bound_extremality() {
    let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));

    assert_eq!(
        AbsFiniteBound::from((pos, BoundExtremality::Start)),
        pos.to_finite_start_bound().to_finite_bound()
    );
    assert_eq!(
        AbsFiniteBound::from((pos, BoundExtremality::End)),
        pos.to_finite_end_bound().to_finite_bound()
    );
}

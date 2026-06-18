use super::bound::*;
use crate::intervals::absolute::{AbsEndBound, AbsFiniteBoundPos, AbsStartBound};
use crate::intervals::meta::{BoundExtremality, BoundInclusivity, HasBoundExtremality};
use crate::test_data::date_timestamp;

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
fn start() {
    assert_eq!(
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
            .to_start_bound()
            .to_bound()
            .start(),
        Some(AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound()),
    );
    assert_eq!(
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
            .to_end_bound()
            .to_bound()
            .start(),
        None,
    );
}

#[test]
fn end() {
    assert_eq!(
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
            .to_start_bound()
            .to_bound()
            .end(),
        None,
    );
    assert_eq!(
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
            .to_end_bound()
            .to_bound()
            .end(),
        Some(AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_end_bound()),
    );
}

#[test]
fn start_inf_past_opposite() {
    assert_eq!(AbsStartBound::InfinitePast.to_bound().opposite(), None);
}

#[test]
fn start_finite_opposite() {
    assert_eq!(
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
            .to_start_bound()
            .to_bound()
            .opposite(),
        Some(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,)
                .to_end_bound()
                .to_bound()
        ),
    );
}

#[test]
fn end_inf_future_opposite() {
    assert_eq!(AbsEndBound::InfiniteFuture.to_bound().opposite(), None);
}

#[test]
fn end_finite_opposite() {
    assert_eq!(
        AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1))
            .to_end_bound()
            .to_bound()
            .opposite(),
        Some(
            AbsFiniteBoundPos::new_with_incl(date_timestamp(2025, 1, 1), BoundInclusivity::Exclusive,)
                .to_start_bound()
                .to_bound()
        ),
    );
}

#[test]
fn equality() {
    let time = date_timestamp(2026, 1, 1);

    assert_eq!(
        AbsFiniteBoundPos::new(time).to_start_bound().to_bound(),
        AbsFiniteBoundPos::new(time).to_start_bound().to_bound()
    );
    assert_eq!(
        AbsFiniteBoundPos::new(time).to_end_bound().to_bound(),
        AbsFiniteBoundPos::new(time).to_end_bound().to_bound()
    );
}

#[test]
fn variant_inequality() {
    let time = date_timestamp(2026, 1, 1);

    assert_ne!(
        AbsFiniteBoundPos::new(time).to_start_bound().to_bound(),
        AbsFiniteBoundPos::new(time).to_end_bound().to_bound()
    );
    assert_ne!(
        AbsFiniteBoundPos::new(time).to_end_bound().to_bound(),
        AbsFiniteBoundPos::new(time).to_start_bound().to_bound(),
    );
}

#[test]
fn bound_extremality() {
    let time = date_timestamp(2026, 1, 1);

    assert_eq!(
        AbsFiniteBoundPos::new(time)
            .to_start_bound()
            .to_bound()
            .bound_extremality(),
        BoundExtremality::Start
    );
    assert_eq!(
        AbsFiniteBoundPos::new(time)
            .to_end_bound()
            .to_bound()
            .bound_extremality(),
        BoundExtremality::End
    );
}

#[test]
fn from_abs_finite_start_bound() {
    assert_eq!(
        AbsBound::from(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound()),
        AbsBound::Start(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound())
    );
}

#[test]
fn from_abs_finite_end_bound() {
    assert_eq!(
        AbsBound::from(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound()),
        AbsBound::End(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound())
    );
}

#[test]
fn from_abs_start_bound() {
    assert_eq!(
        AbsBound::from(AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound()),
        AbsBound::Start(AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_start_bound()),
    );
}

#[test]
fn from_abs_end_bound() {
    assert_eq!(
        AbsBound::from(AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_end_bound()),
        AbsBound::End(AbsFiniteBoundPos::new(date_timestamp(2025, 1, 1)).to_end_bound()),
    );
}

#[test]
fn from_abs_finite_bound() {
    assert_eq!(
        AbsBound::from(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1))
                .to_finite_start_bound()
                .to_finite_bound()
        ),
        AbsBound::Start(AbsStartBound::Finite(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound()
        ))
    );
    assert_eq!(
        AbsBound::from(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1))
                .to_finite_end_bound()
                .to_finite_bound()
        ),
        AbsBound::End(AbsEndBound::Finite(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound()
        ))
    );
}

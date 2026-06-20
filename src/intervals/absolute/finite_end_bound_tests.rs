use std::cmp::Ordering;

use super::finite_end_bound::*;
use crate::intervals::absolute::{AbsBound, AbsEndBound, AbsFiniteBound, AbsFiniteBoundPos};
use crate::intervals::meta::BoundInclusivity;
use crate::test_data::date_timestamp;

#[test]
fn new() {
    let _ = AbsFiniteEndBound::new(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)));
}

#[test]
fn pos() {
    let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
    let finite_end = AbsFiniteEndBound::new(pos);

    assert_eq!(finite_end.pos(), pos);
}

#[test]
fn pos_mut() {
    let mut finite_end = AbsFiniteEndBound::new(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)));
    let _ = finite_end.pos_mut();
}

#[test]
fn opposite() {
    let time = date_timestamp(2026, 1, 1);

    assert_eq!(
        AbsFiniteBoundPos::new(time).to_finite_end_bound().opposite(),
        AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive).to_finite_start_bound(),
    );
}

#[test]
fn to_end_bound() {
    let finite_end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();
    assert_eq!(finite_end.to_end_bound(), AbsEndBound::Finite(finite_end));
}

#[test]
fn to_finite_bound() {
    let finite_end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();
    assert_eq!(finite_end.to_finite_bound(), AbsFiniteBound::End(finite_end));
}

#[test]
fn to_bound() {
    let finite_end = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound();
    assert_eq!(finite_end.to_bound(), AbsBound::End(finite_end.to_end_bound()));
}

mod ord {
    use super::*;

    #[test]
    fn less() {
        assert_eq!(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1))
                .to_finite_end_bound()
                .cmp(&AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound()),
            Ordering::Less
        );
    }

    mod equal {
        use super::*;

        #[test]
        fn inclusive_inclusive() {
            assert_eq!(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Inclusive)
                    .to_finite_end_bound()
                    .cmp(
                        &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Inclusive)
                            .to_finite_end_bound()
                    ),
                Ordering::Equal
            );
        }

        #[test]
        fn inclusive_exclusive() {
            assert_eq!(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Inclusive)
                    .to_finite_end_bound()
                    .cmp(
                        &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                            .to_finite_end_bound()
                    ),
                Ordering::Greater
            );
        }

        #[test]
        fn exclusive_inclusive() {
            assert_eq!(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                    .to_finite_end_bound()
                    .cmp(
                        &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Inclusive)
                            .to_finite_end_bound()
                    ),
                Ordering::Less
            );
        }

        #[test]
        fn exclusive_exclusive() {
            assert_eq!(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                    .to_finite_end_bound()
                    .cmp(
                        &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                            .to_finite_end_bound()
                    ),
                Ordering::Equal
            );
        }
    }

    #[test]
    fn greater() {
        assert_eq!(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2))
                .to_finite_end_bound()
                .cmp(&AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound()),
            Ordering::Greater
        );
    }
}

#[test]
fn from_finite_bound_pos() {
    let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
    assert_eq!(AbsFiniteEndBound::from(pos), AbsFiniteEndBound::new(pos));
}

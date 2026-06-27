use std::cmp::Ordering;

use super::finite_start_bound::*;
use crate::intervals::absolute::{AbsBound, AbsFiniteBound, AbsFiniteBoundPos, AbsStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::test_utils::date_timestamp;

#[test]
fn new() {
    let _ = AbsFiniteStartBound::new(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)));
}

#[test]
fn pos() {
    let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
    let finite_start = AbsFiniteStartBound::new(pos);

    assert_eq!(finite_start.pos(), pos);
}

#[test]
fn pos_mut() {
    let mut finite_start = AbsFiniteStartBound::new(AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)));
    let _ = finite_start.pos_mut();
}

#[test]
fn opposite() {
    let time = date_timestamp(2026, 1, 1);

    assert_eq!(
        AbsFiniteBoundPos::new(time).to_finite_start_bound().opposite(),
        AbsFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive).to_finite_end_bound(),
    );
}

#[test]
fn to_start_bound() {
    let finite_start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
    assert_eq!(finite_start.to_start_bound(), AbsStartBound::Finite(finite_start));
}

#[test]
fn to_finite_bound() {
    let finite_start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
    assert_eq!(finite_start.to_finite_bound(), AbsFiniteBound::Start(finite_start));
}

#[test]
fn to_bound() {
    let finite_start = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound();
    assert_eq!(finite_start.to_bound(), AbsBound::Start(finite_start.to_start_bound()));
}

mod ord {
    use super::*;

    #[test]
    fn less() {
        assert_eq!(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1))
                .to_finite_start_bound()
                .cmp(&AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound()),
            Ordering::Less
        );
    }

    mod equal {
        use super::*;

        #[test]
        fn inclusive_inclusive() {
            assert_eq!(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Inclusive)
                    .to_finite_start_bound()
                    .cmp(
                        &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Inclusive)
                            .to_finite_start_bound()
                    ),
                Ordering::Equal
            );
        }

        #[test]
        fn inclusive_exclusive() {
            assert_eq!(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Inclusive)
                    .to_finite_start_bound()
                    .cmp(
                        &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                            .to_finite_start_bound()
                    ),
                Ordering::Less
            );
        }

        #[test]
        fn exclusive_inclusive() {
            assert_eq!(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                    .to_finite_start_bound()
                    .cmp(
                        &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Inclusive)
                            .to_finite_start_bound()
                    ),
                Ordering::Greater
            );
        }

        #[test]
        fn exclusive_exclusive() {
            assert_eq!(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                    .to_finite_start_bound()
                    .cmp(
                        &AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                            .to_finite_start_bound()
                    ),
                Ordering::Equal
            );
        }
    }

    #[test]
    fn greater() {
        assert_eq!(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2))
                .to_finite_start_bound()
                .cmp(&AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound()),
            Ordering::Greater
        );
    }
}

#[test]
fn from_finite_bound_pos() {
    let pos = AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1));
    assert_eq!(AbsFiniteStartBound::from(pos), AbsFiniteStartBound::new(pos));
}

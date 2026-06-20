use std::cmp::Ordering;

use jiff::SignedDuration;

use super::finite_start_bound::*;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelBound, RelFiniteBound, RelFiniteBoundPos, RelStartBound};

#[test]
fn new() {
    let _ = RelFiniteStartBound::new(RelFiniteBoundPos::new(SignedDuration::from_hours(1)));
}

#[test]
fn pos() {
    let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
    let finite_start = RelFiniteStartBound::new(pos);

    assert_eq!(finite_start.pos(), pos);
}

#[test]
fn pos_mut() {
    let mut finite_start = RelFiniteStartBound::new(RelFiniteBoundPos::new(SignedDuration::from_hours(1)));
    let _ = finite_start.pos_mut();
}

#[test]
fn opposite() {
    let time = SignedDuration::from_hours(1);

    assert_eq!(
        RelFiniteBoundPos::new(time).to_finite_start_bound().opposite(),
        RelFiniteBoundPos::new_with_incl(time, BoundInclusivity::Exclusive).to_finite_end_bound(),
    );
}

#[test]
fn to_start_bound() {
    let finite_start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
    assert_eq!(finite_start.to_start_bound(), RelStartBound::Finite(finite_start));
}

#[test]
fn to_finite_bound() {
    let finite_start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
    assert_eq!(finite_start.to_finite_bound(), RelFiniteBound::Start(finite_start));
}

#[test]
fn to_bound() {
    let finite_start = RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound();
    assert_eq!(finite_start.to_bound(), RelBound::Start(finite_start.to_start_bound()));
}

mod ord {
    use super::*;

    #[test]
    fn less() {
        assert_eq!(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1))
                .to_finite_start_bound()
                .cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound()),
            Ordering::Less
        );
    }

    mod equal {
        use super::*;

        #[test]
        fn inclusive_inclusive() {
            assert_eq!(
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
                    .to_finite_start_bound()
                    .cmp(
                        &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
                            .to_finite_start_bound()
                    ),
                Ordering::Equal
            );
        }

        #[test]
        fn inclusive_exclusive() {
            assert_eq!(
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
                    .to_finite_start_bound()
                    .cmp(
                        &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                            .to_finite_start_bound()
                    ),
                Ordering::Less
            );
        }

        #[test]
        fn exclusive_inclusive() {
            assert_eq!(
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                    .to_finite_start_bound()
                    .cmp(
                        &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Inclusive)
                            .to_finite_start_bound()
                    ),
                Ordering::Greater
            );
        }

        #[test]
        fn exclusive_exclusive() {
            assert_eq!(
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                    .to_finite_start_bound()
                    .cmp(
                        &RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                            .to_finite_start_bound()
                    ),
                Ordering::Equal
            );
        }
    }

    #[test]
    fn greater() {
        assert_eq!(
            RelFiniteBoundPos::new(SignedDuration::from_hours(2))
                .to_finite_start_bound()
                .cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound()),
            Ordering::Greater
        );
    }
}

#[test]
fn from_finite_bound_pos() {
    let pos = RelFiniteBoundPos::new(SignedDuration::from_hours(1));
    assert_eq!(RelFiniteStartBound::from(pos), RelFiniteStartBound::new(pos));
}

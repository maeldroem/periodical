use jiff::SignedDuration;

use super::rel_state_change::*;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
use crate::iter::intervals::layered_bounds::state::LayeredBoundsState;

#[test]
fn at_rel_bound_old_state() {
    assert_eq!(
        LayeredBoundsStateChangeAtRelativeBound::new(
            LayeredBoundsState::FirstLayer,
            LayeredBoundsState::SecondLayer,
            None,
            None,
        )
        .old_state(),
        LayeredBoundsState::FirstLayer,
    );
}

#[test]
fn at_rel_bound_new_state() {
    assert_eq!(
        LayeredBoundsStateChangeAtRelativeBound::new(
            LayeredBoundsState::FirstLayer,
            LayeredBoundsState::SecondLayer,
            None,
            None,
        )
        .new_state(),
        LayeredBoundsState::SecondLayer,
    );
}

#[test]
fn at_rel_bound_old_state_end() {
    assert_eq!(
        LayeredBoundsStateChangeAtRelativeBound::new(
            LayeredBoundsState::FirstLayer,
            LayeredBoundsState::SecondLayer,
            Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            ))),
            Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ))),
        )
        .old_state_end(),
        Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn at_rel_bound_new_state_start() {
    assert_eq!(
        LayeredBoundsStateChangeAtRelativeBound::new(
            LayeredBoundsState::FirstLayer,
            LayeredBoundsState::SecondLayer,
            Some(RelativeEndBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Inclusive,
            ))),
            Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ))),
        )
        .new_state_start(),
        Some(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            SignedDuration::from_hours(1),
            BoundInclusivity::Exclusive,
        ))),
    );
}

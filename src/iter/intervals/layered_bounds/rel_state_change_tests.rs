use jiff::SignedDuration;

use super::rel_state_change::*;
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::RelativeFiniteBound;
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
            Some(
                RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                    .to_end_bound()
            ),
            Some(
                RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                    .to_start_bound()
            ),
        )
        .old_state_end(),
        Some(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                .to_end_bound()
        ),
    );
}

#[test]
fn at_rel_bound_new_state_start() {
    assert_eq!(
        LayeredBoundsStateChangeAtRelativeBound::new(
            LayeredBoundsState::FirstLayer,
            LayeredBoundsState::SecondLayer,
            Some(
                RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Inclusive,)
                    .to_end_bound()
            ),
            Some(
                RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                    .to_start_bound()
            ),
        )
        .new_state_start(),
        Some(
            RelativeFiniteBound::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive,)
                .to_start_bound()
        ),
    );
}

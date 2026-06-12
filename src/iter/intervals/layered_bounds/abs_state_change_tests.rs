use std::error::Error;

use jiff::Zoned;

use super::abs_state_change::*;
use crate::intervals::absolute::AbsFiniteBoundPos;
use crate::intervals::meta::BoundInclusivity;
use crate::iter::intervals::layered_bounds::state::LayeredBoundsState;

#[test]
fn at_abs_bound_old_state() {
    assert_eq!(
        LayeredBoundsStateChangeAtAbsBound::new(
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
fn at_abs_bound_new_state() {
    assert_eq!(
        LayeredBoundsStateChangeAtAbsBound::new(
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
fn at_abs_bound_old_state_end() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        LayeredBoundsStateChangeAtAbsBound::new(
            LayeredBoundsState::FirstLayer,
            LayeredBoundsState::SecondLayer,
            Some(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound()
            ),
            Some(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
            ),
        )
        .old_state_end(),
        Some(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .to_end_bound()
        ),
    );

    Ok(())
}

#[test]
fn at_abs_bound_new_state_start() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        LayeredBoundsStateChangeAtAbsBound::new(
            LayeredBoundsState::FirstLayer,
            LayeredBoundsState::SecondLayer,
            Some(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound()
            ),
            Some(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
            ),
        )
        .new_state_start(),
        Some(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
        ),
    );

    Ok(())
}

use chrono::Utc;

use super::grow::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds
};
use crate::test_utils::date;

#[test]
fn grow_start_emptiable_abs_bounds_empty() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.grow_start(AbsoluteStartBound::InfinitePast),
        EmptiableAbsoluteBounds::Empty,
    );
}

#[test]
fn grow_end_emptiable_abs_bounds_empty() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.grow_end(AbsoluteEndBound::InfiniteFuture),
        EmptiableAbsoluteBounds::Empty,
    );
}

#[test]
fn grow_start_to_finite_open_interval() {
    assert_eq!(
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
            .grow_start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))),
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    );
}

#[test]
fn grow_end_to_finite_open_interval() {
    assert_eq!(
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
            .grow_end(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))),
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    );
}

#[test]
fn grow_start_to_inside_abs_bounds_closed() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)))
        )
            .grow_start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)))
        ),
    );
}

#[test]
fn grow_end_to_inside_abs_bounds_closed() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)))
        )
            .grow_end(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)))
        ),
    );
}

#[test]
fn grow_start_to_outside_abs_bounds_closed() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)))
        )
            .grow_start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)))
        ),
    );
}

#[test]
fn grow_end_to_outside_abs_bounds_closed() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
        )
            .grow_end(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)))),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)))
        ),
    );
}


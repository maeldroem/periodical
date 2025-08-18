use chrono::Utc;

use super::shrink::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBounds,
};
use crate::test_utils::date;

#[test]
fn shrink_start_emptiable_abs_bounds_empty() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.shrink_start(AbsoluteStartBound::InfinitePast),
        EmptiableAbsoluteBounds::Empty,
    );
}

#[test]
fn shrink_end_emptiable_abs_bounds_empty() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.shrink_end(AbsoluteEndBound::InfiniteFuture),
        EmptiableAbsoluteBounds::Empty,
    );
}

#[test]
fn shrink_start_to_finite_open_interval() {
    assert_eq!(
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).shrink_start(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::InfiniteFuture,
        ),
    );
}

#[test]
fn shrink_end_to_finite_open_interval() {
    assert_eq!(
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture).shrink_end(
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1)))
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        ),
    );
}

#[test]
fn shrink_start_to_inside_abs_bounds_closed() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)))
        )
        .shrink_start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 2
        )))),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)))
        ),
    );
}

#[test]
fn shrink_end_to_inside_abs_bounds_closed() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)))
        )
        .shrink_end(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 2
        )))),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
        ),
    );
}

#[test]
fn shrink_start_to_outside_abs_bounds_closed() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)))
        )
        .shrink_start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 1
        )))),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3)))
        ),
    );
}

#[test]
fn shrink_end_to_outside_abs_bounds_closed() {
    assert_eq!(
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
        )
        .shrink_end(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 3
        )))),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2)))
        ),
    );
}

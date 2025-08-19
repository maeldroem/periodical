use chrono::{Duration, Utc};

use crate::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::relative::{RelativeEndBound, RelativeFiniteBound, RelativeStartBound};
use crate::prelude::{AbsoluteBounds, RelativeBounds};
use crate::test_utils::date;

use super::relativity_conversion::*;

#[test]
fn create_to_absolute_iter() {
    let relative_intervals = [
        RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::zero())),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::days(1))),
        ),
    ];

    relative_intervals.to_absolute(date(&Utc, 2025, 1, 1));
}

#[test]
fn create_to_relative_iter() {
    let absolute_intervals = [
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        ),
    ];

    absolute_intervals.to_relative(date(&Utc, 2025, 1, 1));
}

#[test]
fn to_absolute_iter_run() {
    let relative_intervals = [
        RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::zero())),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::days(1))),
        ),
    ];

    assert_eq!(
        relative_intervals
            .to_absolute(date(&Utc, 2025, 1, 1))
            .collect::<Vec<_>>(),
        vec![
            AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
            ),
        ],
    );
}

#[test]
fn to_relative_iter_run() {
    let absolute_intervals = [
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        ),
    ];

    assert_eq!(
        absolute_intervals
            .to_relative(date(&Utc, 2025, 1, 1))
            .collect::<Vec<_>>(),
        vec![
            RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::zero())),
                RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::days(1))),
            ),
        ],
    );
}

#[test]
fn to_absolute_iter_run_reverse() {
    let relative_intervals = [
        RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::zero())),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::days(1))),
        ),
    ];

    assert_eq!(
        relative_intervals
            .to_absolute(date(&Utc, 2025, 1, 1))
            .rev()
            .collect::<Vec<_>>(),
        vec![
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
            ),
            AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
        ],
    );
}

#[test]
fn to_relative_iter_run_reverse() {
    let absolute_intervals = [
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        ),
    ];

    assert_eq!(
        absolute_intervals
            .to_relative(date(&Utc, 2025, 1, 1))
            .rev()
            .collect::<Vec<_>>(),
        vec![
            RelativeBounds::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::zero())),
                RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::days(1))),
            ),
            RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
        ],
    );
}

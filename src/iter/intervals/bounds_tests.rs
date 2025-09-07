use chrono::{Duration, Utc};

use crate::intervals::absolute::{
    AbsoluteBound, AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
};
use crate::intervals::relative::{
    RelativeBound, RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
};
use crate::test_utils::date;

use super::bounds::*;

#[test]
fn create_abs_bounds_iter() {
    let data = [
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
        ),
    ];

    let _ = AbsoluteBoundsIter::new(data.into_iter());
}

#[test]
fn abs_bounds_iter_run() {
    let data = [
        AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2024, 1, 1))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 6))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 9))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 4))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 10))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 6))),
            AbsoluteEndBound::InfiniteFuture,
        ),
    ];

    assert_eq!(
        AbsoluteBoundsIter::new(data.into_iter()).collect::<Vec<_>>(),
        vec![
            AbsoluteBound::Start(AbsoluteStartBound::InfinitePast),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2024, 1, 1
            )))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 1, 1
            )))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 1, 6
            )))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 1, 3
            )))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 1, 9
            )))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 2, 1
            )))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 2, 4
            )))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 2, 5
            )))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 2, 10
            )))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 2, 6
            )))),
            AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture),
        ],
    );
}

#[test]
fn create_rel_bounds_iter() {
    let data = [
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(3))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(5))),
        ),
    ];

    let _ = RelativeBoundsIter::new(data.into_iter());
}

#[test]
fn rel_bounds_iter_run() {
    let data = [
        RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(10))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(15))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(13))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(19))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(20))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(24))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(25))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(29))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(27))),
            RelativeEndBound::InfiniteFuture,
        ),
    ];

    assert_eq!(
        RelativeBoundsIter::new(data.into_iter()).collect::<Vec<_>>(),
        vec![
            RelativeBound::Start(RelativeStartBound::InfinitePast),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                10
            )))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(15)))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                13
            )))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(19)))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                20
            )))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(24)))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                25
            )))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(29)))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                27
            )))),
            RelativeBound::End(RelativeEndBound::InfiniteFuture),
        ],
    );
}

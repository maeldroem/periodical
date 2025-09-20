use chrono::{Duration, Utc};

use crate::intervals::absolute::{
    AbsoluteBound, AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{
    RelativeBound, RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
};
use crate::iter::intervals::bounds::{AbsoluteBoundsIteratorDispatcher, RelativeBoundsIteratorDispatcher};
use crate::test_utils::date;

use super::united_bounds::*;

#[test]
fn create_abs_united_bounds_iter() {
    let data = [
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 6))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2024, 1, 1))),
            AbsoluteEndBound::InfiniteFuture,
        ),
    ];

    let _ = AbsoluteUnitedBoundsIter::new(data.abs_bounds_iter());
}

#[test]
fn abs_united_bounds_run() {
    let mut data = [
        AbsoluteBound::Start(AbsoluteStartBound::InfinitePast),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2024, 1, 1,
        )))),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 2,
        )))),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 5,
        )))),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 10,
        )))),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 20,
        )))),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 10,
        )))),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 12,
        )))),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 11,
        )))),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 15,
        )))),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 13,
        )))),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 17,
        )))),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 19,
        )))),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 25,
        )))),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 25),
            BoundInclusivity::Exclusive,
        ))),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 1, 30,
        )))),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 2, 1,
        )))),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 2, 5,
        )))),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 2, 4,
        )))),
        AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture),
        AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 5, 1,
        )))),
        AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
            &Utc, 2025, 6, 1,
        )))),
    ];

    data.sort();

    assert_eq!(
        AbsoluteUnitedBoundsIter::new(data.into_iter()).collect::<Vec<_>>(),
        vec![
            AbsoluteBound::Start(AbsoluteStartBound::InfinitePast),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2024, 1, 1
            )))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 1, 2
            )))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 1, 5
            )))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 1, 10
            )))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 1, 30
            )))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 2, 1
            )))),
            AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture),
        ],
    );
}

#[test]
fn abs_united_bounds_run_from_abs_bounds_iter() {
    let data = [
        AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2024, 1, 1))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 20))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 12))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 11))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 15))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 13))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 17))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 19))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 25))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                date(&Utc, 2025, 1, 25),
                BoundInclusivity::Exclusive,
            )),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 30))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 4))),
            AbsoluteEndBound::InfiniteFuture,
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 6, 1))),
        ),
    ];

    assert_eq!(
        data.abs_bounds_iter().unite_bounds().collect::<Vec<_>>(),
        vec![
            AbsoluteBound::Start(AbsoluteStartBound::InfinitePast),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2024, 1, 1
            )))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 1, 2
            )))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 1, 5
            )))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 1, 10
            )))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 1, 30
            )))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(
                &Utc, 2025, 2, 1
            )))),
            AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture),
        ],
    );
}

#[test]
fn create_rel_united_bounds_iter() {
    let data = [
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(11))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(12))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(16))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(19))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
            RelativeEndBound::InfiniteFuture,
        ),
    ];

    let _ = RelativeUnitedBoundsIter::new(data.rel_bounds_iter());
}

#[test]
fn rel_united_bounds_run() {
    let mut data = [
        RelativeBound::Start(RelativeStartBound::InfinitePast),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            12,
        )))),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(15)))),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            20,
        )))),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(30)))),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            20,
        )))),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(22)))),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            21,
        )))),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(25)))),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            23,
        )))),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(27)))),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            29,
        )))),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(35)))),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
            Duration::hours(35),
            BoundInclusivity::Exclusive,
        ))),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(40)))),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            50,
        )))),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(55)))),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            54,
        )))),
        RelativeBound::End(RelativeEndBound::InfiniteFuture),
        RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
            101,
        )))),
        RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(201)))),
    ];

    data.sort();

    assert_eq!(
        RelativeUnitedBoundsIter::new(data.into_iter()).collect::<Vec<_>>(),
        vec![
            RelativeBound::Start(RelativeStartBound::InfinitePast),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                12
            )))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(15)))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                20
            )))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(40)))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                50
            )))),
            RelativeBound::End(RelativeEndBound::InfiniteFuture),
        ],
    );
}

#[test]
fn rel_united_bounds_run_from_rel_bounds_iter() {
    let data = [
        RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(12))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(15))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(20))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(30))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(20))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(22))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(21))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(25))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(23))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(27))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(29))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(35))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                Duration::hours(35),
                BoundInclusivity::Exclusive,
            )),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(40))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(50))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(55))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(54))),
            RelativeEndBound::InfiniteFuture,
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(101))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(201))),
        ),
    ];

    assert_eq!(
        data.rel_bounds_iter().unite_bounds().collect::<Vec<_>>(),
        vec![
            RelativeBound::Start(RelativeStartBound::InfinitePast),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(1)))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                12
            )))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(15)))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                20
            )))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(40)))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(
                50
            )))),
            RelativeBound::End(RelativeEndBound::InfiniteFuture),
        ],
    );
}

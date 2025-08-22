use chrono::Utc;

use crate::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::prelude::BoundContainmentRuleSet;
use crate::prelude::AbsoluteBounds;
use crate::test_utils::date;

use super::united_set::*;

#[test]
fn new_absolute_united_set() {
    let _ = AbsoluteUnitedIntervalSet::new();
}

#[test]
fn absolute_united_set_insert_first() {
    let mut set = AbsoluteUnitedIntervalSet::new();

    set.insert(&AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
    ));

    assert_eq!(
        set.into_iter().collect::<Vec<_>>(),
        vec![
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
            ),
        ],
    );
}

#[test]
fn absolute_united_set_insert_multiple() {
    let mut set = AbsoluteUnitedIntervalSet::new();

    set.insert(&AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 3))),
    ));

    set.insert(&AbsoluteBounds::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2024, 1, 1))),
    ));

    set.insert(&AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2024, 5, 1))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2024, 5, 10))),
    ));

    set.insert(&AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 1, 6),
            BoundInclusivity::Exclusive
        )),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
    ));

    set.insert(&AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 1))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 6))),
    ));

    set.insert(&AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 6))),
    ));

    println!("actual: {:#?} \n expected: {:#?}", set.clone().into_iter().collect::<Vec<_>>(), vec![
        AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2024, 1, 1))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2024, 5, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2024, 5, 10))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 6))),
        ),
    ]);

    assert_eq!(
        set.into_iter().collect::<Vec<_>>(),
        vec![
            AbsoluteBounds::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2024, 1, 1))),
            ),
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2024, 5, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2024, 5, 10))),
            ),
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 10))),
            ),
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 6))),
            ),
        ],
    );
}

#[test]
fn absolute_united_set_remove_intervals() {
    let mut set = AbsoluteUnitedIntervalSet::new();

    set.insert(&AbsoluteBounds::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
    ));

    set.insert(&AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 2))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 5))),
    ));

    set.insert(&AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 1))),
        AbsoluteEndBound::InfiniteFuture,
    ));

    assert!(set.remove(&AbsoluteBounds::new(
        AbsoluteStartBound::InfinitePast,
        // End time shouldn't matter
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
    )));

    assert!(set.remove(&AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 2))),
        AbsoluteEndBound::InfiniteFuture,
    )));

    assert!(!set.remove(&AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2026, 1, 1))),
        AbsoluteEndBound::InfiniteFuture,
    )));

    assert_eq!(
        set.into_iter().collect::<Vec<_>>(),
        vec![
            AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 1))),
                AbsoluteEndBound::InfiniteFuture,
            ),
        ],
    );
}

#[test]
fn absolute_united_set_overlapping_intervals() {
    let mut set = AbsoluteUnitedIntervalSet::new();

    set.insert(&AbsoluteBounds::new(
        AbsoluteStartBound::InfinitePast,
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 2))),
    ));

    set.insert(&AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 1))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 3))),
    ));

    set.insert(&AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 4))),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 10))),
    ));

    set.insert(&AbsoluteBounds::new(
        AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
            date(&Utc, 2025, 5, 1),
            BoundInclusivity::Exclusive,
        )),
        AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 2))),
    ));

    assert_eq!(
        set.overlapping_intervals(
            &AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 5))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 1))),
            ),
            BoundContainmentRuleSet::Strict,
        ).collect::<Vec<_>>(),
        vec![
            &AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 1))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 3))),
            ),
            &AbsoluteBounds::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 4))),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 3, 10))),
            ),
        ],
    );
}

#[test]
fn absolute_united_set_intersect() {
    let mut set = AbsoluteUnitedIntervalSet::new();
}

#[test]
fn absolute_united_set_difference() {

}

#[test]
fn absolute_united_set_sym_difference() {

}

#[test]
fn absolute_united_set_to_relative() {

}

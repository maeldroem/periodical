use chrono::{Duration, Utc};

use crate::intervals::absolute::{
    AbsoluteBound, AbsoluteBounds, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound,
};
use crate::intervals::relative::{
    RelativeBound, RelativeBounds, RelativeEndBound, RelativeFiniteBound, RelativeStartBound,
};
use crate::test_utils::date;

use super::bound_position::*;

#[test]
fn default_bound_position() {
    assert_eq!(BoundPosition::default(), BoundPosition::MIN);
}

#[test]
fn bound_position_index_of_start() {
    assert_eq!(BoundPosition::Start(51907).index(), 51907);
}

#[test]
fn bound_position_index_of_end() {
    assert_eq!(BoundPosition::End(8976).index(), 8976);
}

#[test]
fn bound_position_get_abs_bound_of_start_inside() {
    let data = [
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 4))),
        ),
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    ];

    assert_eq!(
        BoundPosition::Start(2).get_abs_bound(data.iter()),
        Some(AbsoluteBound::Start(AbsoluteStartBound::Finite(
            AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 1))
        ))),
    );
}

#[test]
fn bound_position_get_abs_bound_of_start_outside() {
    let data = [
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 4))),
        ),
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    ];

    assert_eq!(BoundPosition::Start(5).get_abs_bound(data.iter()), None,);
}

#[test]
fn bound_position_get_abs_bound_of_end_inside() {
    let data = [
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 4))),
        ),
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    ];

    assert_eq!(
        BoundPosition::End(2).get_abs_bound(data.iter()),
        Some(AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
            date(&Utc, 2025, 5, 4)
        )))),
    );
}

#[test]
fn bound_position_get_abs_bound_of_end_outside() {
    let data = [
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 2, 5))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 1, 1))),
        ),
        AbsoluteBounds::new(
            AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 1))),
            AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(date(&Utc, 2025, 5, 4))),
        ),
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    ];

    assert_eq!(BoundPosition::End(5).get_abs_bound(data.iter()), None,);
}

#[test]
fn bound_position_get_rel_bound_of_start_inside() {
    let data = [
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(21))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(25))),
        ),
        RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(11))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(51))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(54))),
        ),
        RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
    ];

    assert_eq!(
        BoundPosition::Start(2).get_rel_bound(data.iter()),
        Some(RelativeBound::Start(RelativeStartBound::Finite(
            RelativeFiniteBound::new(Duration::hours(51))
        ))),
    );
}

#[test]
fn bound_position_get_rel_bound_of_start_outside() {
    let data = [
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(21))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(25))),
        ),
        RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(11))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(51))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(54))),
        ),
        RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
    ];

    assert_eq!(BoundPosition::Start(5).get_rel_bound(data.iter()), None,);
}

#[test]
fn bound_position_get_rel_bound_of_end_inside() {
    let data = [
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(21))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(25))),
        ),
        RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(11))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(51))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(54))),
        ),
        RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
    ];

    assert_eq!(
        BoundPosition::End(2).get_rel_bound(data.iter()),
        Some(RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
            Duration::hours(54)
        )))),
    );
}

#[test]
fn bound_position_get_rel_bound_of_end_outside() {
    let data = [
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(21))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(25))),
        ),
        RelativeBounds::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(11))),
        ),
        RelativeBounds::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(Duration::hours(51))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(Duration::hours(54))),
        ),
        RelativeBounds::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
    ];

    assert_eq!(BoundPosition::End(5).get_rel_bound(data.iter()), None,);
}

#[test]
fn bound_position_add_bounds_index_on_start_no_overflow() {
    let mut position = BoundPosition::Start(5);

    assert!(!position.add_interval_index(3));
    assert_eq!(position, BoundPosition::Start(8));
}

#[test]
fn bound_position_add_bounds_index_on_start_overflow() {
    let mut position = BoundPosition::Start(5);

    assert!(position.add_interval_index(usize::MAX));
    assert_eq!(position, BoundPosition::MAX);
}

#[test]
fn bound_position_add_bounds_index_on_end_no_overflow() {
    let mut position = BoundPosition::End(5);

    assert!(!position.add_interval_index(3));
    assert_eq!(position, BoundPosition::End(8));
}

#[test]
fn bound_position_add_bounds_index_on_end_overflow() {
    let mut position = BoundPosition::End(5);

    assert!(position.add_interval_index(usize::MAX));
    assert_eq!(position, BoundPosition::MAX);
}

#[test]
fn bound_position_sub_bounds_index_on_start_no_underflow() {
    let mut position = BoundPosition::Start(8);

    assert!(!position.sub_interval_index(3));
    assert_eq!(position, BoundPosition::Start(5));
}

#[test]
fn bound_position_sub_bounds_index_on_start_underflow() {
    let mut position = BoundPosition::Start(8);

    assert!(position.sub_interval_index(9));
    assert_eq!(position, BoundPosition::MIN);
}

#[test]
fn bound_position_sub_bounds_index_on_end_no_underflow() {
    let mut position = BoundPosition::End(8);

    assert!(!position.sub_interval_index(3));
    assert_eq!(position, BoundPosition::End(5));
}

#[test]
fn bound_position_sub_bounds_index_on_end_underflow() {
    let mut position = BoundPosition::End(8);

    assert!(position.sub_interval_index(9));
    assert_eq!(position, BoundPosition::MIN);
}

#[test]
fn bound_position_increment_bounds_index_start_no_overflow() {
    let mut position = BoundPosition::Start(8);

    assert!(!position.increment_interval_index());
    assert_eq!(position, BoundPosition::Start(9));
}

#[test]
fn bound_position_increment_bounds_index_start_overflow() {
    let mut position = BoundPosition::Start(usize::MAX);

    assert!(position.increment_interval_index());
    assert_eq!(position, BoundPosition::MAX);
}

#[test]
fn bound_position_increment_bounds_index_end_no_overflow() {
    let mut position = BoundPosition::End(8);

    assert!(!position.increment_interval_index());
    assert_eq!(position, BoundPosition::End(9));
}

#[test]
fn bound_position_increment_bounds_index_end_overflow() {
    let mut position = BoundPosition::End(usize::MAX);

    assert!(position.increment_interval_index());
    assert_eq!(position, BoundPosition::MAX);
}

#[test]
fn bound_position_decrement_bounds_index_start_no_underflow() {
    let mut position = BoundPosition::Start(6);

    assert!(!position.decrement_interval_index());
    assert_eq!(position, BoundPosition::Start(5));
}

#[test]
fn bound_position_decrement_bounds_index_start_underflow() {
    let mut position = BoundPosition::Start(usize::MIN);

    assert!(position.decrement_interval_index());
    assert_eq!(position, BoundPosition::MIN);
}

#[test]
fn bound_position_decrement_bounds_index_end_no_underflow() {
    let mut position = BoundPosition::End(6);

    assert!(!position.decrement_interval_index());
    assert_eq!(position, BoundPosition::End(5));
}

#[test]
fn bound_position_decrement_bounds_index_end_underflow() {
    let mut position = BoundPosition::End(usize::MIN);

    assert!(position.decrement_interval_index());
    assert_eq!(position, BoundPosition::MIN);
}

#[test]
fn bound_position_advance_by_8_start_no_overflow() {
    let mut position = BoundPosition::Start(5);

    assert!(!position.advance_by(8));
    assert_eq!(position, BoundPosition::Start(9));
}

#[test]
fn bound_position_advance_by_7_start_no_overflow() {
    let mut position = BoundPosition::Start(5);

    assert!(!position.advance_by(7));
    assert_eq!(position, BoundPosition::End(8));
}

#[test]
fn bound_position_advance_by_start_overflow() {
    let mut position = BoundPosition::Start(5);

    assert!(!position.advance_by(usize::MAX));
    assert!(position.advance_by(usize::MAX));
    assert_eq!(position, BoundPosition::MAX);
}

#[test]
fn bound_position_advance_by_8_end_no_overflow() {
    let mut position = BoundPosition::End(5);

    assert!(!position.advance_by(8));
    assert_eq!(position, BoundPosition::End(9));
}

#[test]
fn bound_position_advance_by_7_end_no_overflow() {
    let mut position = BoundPosition::End(5);

    assert!(!position.advance_by(7));
    assert_eq!(position, BoundPosition::Start(9));
}

#[test]
fn bound_position_advance_by_end_overflow() {
    let mut position = BoundPosition::End(5);

    assert!(!position.advance_by(usize::MAX));
    assert!(position.advance_by(usize::MAX));
    assert_eq!(position, BoundPosition::MAX);
}

#[test]
fn bound_position_advance_back_by_8_start_no_underflow() {
    let mut position = BoundPosition::Start(10);

    assert!(!position.advance_back_by(8));
    assert_eq!(position, BoundPosition::Start(6));
}

#[test]
fn bound_position_advance_back_by_7_start_no_underflow() {
    let mut position = BoundPosition::Start(10);

    assert!(!position.advance_back_by(7));
    assert_eq!(position, BoundPosition::End(6));
}

#[test]
fn bound_position_advance_back_by_start_underflow() {
    let mut position = BoundPosition::Start(10);

    assert!(position.advance_back_by(30));
    assert_eq!(position, BoundPosition::MIN);
}

#[test]
fn bound_position_advance_back_by_8_end_no_underflow() {
    let mut position = BoundPosition::End(10);

    assert!(!position.advance_back_by(8));
    assert_eq!(position, BoundPosition::End(6));
}

#[test]
fn bound_position_advance_back_by_7_end_no_underflow() {
    let mut position = BoundPosition::End(10);

    assert!(!position.advance_back_by(7));
    assert_eq!(position, BoundPosition::Start(7));
}

#[test]
fn bound_position_advance_back_by_end_underflow() {
    let mut position = BoundPosition::End(10);

    assert!(position.advance_back_by(30));
    assert_eq!(position, BoundPosition::MIN);
}

#[test]
fn bound_position_next_bound_start_no_overflow() {
    let mut position = BoundPosition::Start(5);

    assert!(!position.next_bound());
    assert_eq!(position, BoundPosition::End(5));
}

#[test]
fn bound_position_next_bound_start_at_usize_max() {
    let mut position = BoundPosition::Start(usize::MAX);

    assert!(!position.next_bound());
    assert_eq!(position, BoundPosition::End(usize::MAX));
}

#[test]
fn bound_position_next_bound_end_no_overflow() {
    let mut position = BoundPosition::End(5);

    assert!(!position.next_bound());
    assert_eq!(position, BoundPosition::Start(6));
}

#[test]
fn bound_position_next_bound_end_overflow() {
    let mut position = BoundPosition::End(usize::MAX);

    assert!(position.next_bound());
    assert_eq!(position, BoundPosition::MAX);
}

#[test]
fn bound_position_prev_bound_start_no_underflow() {
    let mut position = BoundPosition::Start(5);

    assert!(!position.prev_bound());
    assert_eq!(position, BoundPosition::End(4));
}

#[test]
fn bound_position_prev_bound_start_underflow() {
    let mut position = BoundPosition::Start(usize::MIN);

    assert!(position.prev_bound());
    assert_eq!(position, BoundPosition::MIN);
}

#[test]
fn bound_position_prev_bound_end_no_underflow() {
    let mut position = BoundPosition::End(5);

    assert!(!position.prev_bound());
    assert_eq!(position, BoundPosition::Start(5));
}

#[test]
fn bound_position_prev_bound_end_usize_min_no_underflow() {
    let mut position = BoundPosition::End(usize::MIN);

    assert!(!position.prev_bound());
    assert_eq!(position, BoundPosition::Start(usize::MIN));
}

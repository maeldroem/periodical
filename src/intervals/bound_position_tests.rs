use std::error::Error;

use jiff::{SignedDuration, Timestamp};

use super::bound_position::*;
use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::relative::{RelativeBoundPair, RelativeEndBound, RelativeFiniteBound, RelativeStartBound};

#[test]
fn default_bound_position() {
    assert_eq!(BoundPosition::default(), BoundPosition::MIN);
}

#[test]
fn index_of_start() {
    assert_eq!(BoundPosition::Start(51907).index(), 51907);
}

#[test]
fn index_of_end() {
    assert_eq!(BoundPosition::End(8976).index(), 8976);
}

#[test]
fn get_abs_bound_of_start_inside() -> Result<(), Box<dyn Error>> {
    let data = [
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-02-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2025-02-05 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-05-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2025-05-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    ];

    assert_eq!(
        BoundPosition::Start(2).get_abs_bound(data.iter()),
        Some(
            AbsoluteFiniteBound::new("2025-05-01 00:00:00Z".parse::<Timestamp>()?)
                .to_start_bound()
                .to_bound()
        ),
    );
    Ok(())
}

#[test]
fn get_abs_bound_of_start_outside() -> Result<(), Box<dyn Error>> {
    let data = [
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-02-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2025-02-05 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-05-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2025-05-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    ];

    assert_eq!(BoundPosition::Start(5).get_abs_bound(data.iter()), None);
    Ok(())
}

#[test]
fn get_abs_bound_of_end_inside() -> Result<(), Box<dyn Error>> {
    let data = [
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-02-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2025-02-05 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-05-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2025-05-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    ];

    assert_eq!(
        BoundPosition::End(2).get_abs_bound(data.iter()),
        Some(
            AbsoluteFiniteBound::new("2025-05-04 00:00:00Z".parse::<Timestamp>()?)
                .to_end_bound()
                .to_bound()
        ),
    );
    Ok(())
}

#[test]
fn get_abs_bound_of_end_outside() -> Result<(), Box<dyn Error>> {
    let data = [
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-02-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2025-02-05 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        AbsoluteBoundPair::new(
            AbsoluteStartBound::InfinitePast,
            AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new("2025-05-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
            AbsoluteFiniteBound::new("2025-05-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
        ),
        AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    ];

    assert_eq!(BoundPosition::End(5).get_abs_bound(data.iter()), None);
    Ok(())
}

#[test]
fn get_rel_bound_of_start_inside() {
    let data = [
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(21)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(25)).to_end_bound(),
        ),
        RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBound::new(SignedDuration::from_hours(11)).to_end_bound(),
        ),
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(51)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(54)).to_end_bound(),
        ),
        RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
    ];

    assert_eq!(
        BoundPosition::Start(2).get_rel_bound(data.iter()),
        Some(
            RelativeFiniteBound::new(SignedDuration::from_hours(51))
                .to_start_bound()
                .to_bound()
        ),
    );
}

#[test]
fn get_rel_bound_of_start_outside() {
    let data = [
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(21)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(25)).to_end_bound(),
        ),
        RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBound::new(SignedDuration::from_hours(11)).to_end_bound(),
        ),
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(51)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(54)).to_end_bound(),
        ),
        RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
    ];

    assert_eq!(BoundPosition::Start(5).get_rel_bound(data.iter()), None);
}

#[test]
fn get_rel_bound_of_end_inside() {
    let data = [
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(21)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(25)).to_end_bound(),
        ),
        RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBound::new(SignedDuration::from_hours(11)).to_end_bound(),
        ),
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(51)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(54)).to_end_bound(),
        ),
        RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
    ];

    assert_eq!(
        BoundPosition::End(2).get_rel_bound(data.iter()),
        Some(
            RelativeFiniteBound::new(SignedDuration::from_hours(54))
                .to_end_bound()
                .to_bound()
        ),
    );
}

#[test]
fn get_rel_bound_of_end_outside() {
    let data = [
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(21)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(25)).to_end_bound(),
        ),
        RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBound::new(SignedDuration::from_hours(11)).to_end_bound(),
        ),
        RelativeBoundPair::new(
            RelativeFiniteBound::new(SignedDuration::from_hours(51)).to_start_bound(),
            RelativeFiniteBound::new(SignedDuration::from_hours(54)).to_end_bound(),
        ),
        RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
    ];

    assert_eq!(BoundPosition::End(5).get_rel_bound(data.iter()), None);
}

#[test]
fn add_bounds_index_on_start_no_overflow() {
    let mut position = BoundPosition::Start(5);

    assert!(!position.add_interval_index(3));
    assert_eq!(position, BoundPosition::Start(8));
}

#[test]
fn add_bounds_index_on_start_overflow() {
    let mut position = BoundPosition::Start(5);

    assert!(position.add_interval_index(usize::MAX));
    assert_eq!(position, BoundPosition::MAX);
}

#[test]
fn add_bounds_index_on_end_no_overflow() {
    let mut position = BoundPosition::End(5);

    assert!(!position.add_interval_index(3));
    assert_eq!(position, BoundPosition::End(8));
}

#[test]
fn add_bounds_index_on_end_overflow() {
    let mut position = BoundPosition::End(5);

    assert!(position.add_interval_index(usize::MAX));
    assert_eq!(position, BoundPosition::MAX);
}

#[test]
fn sub_bounds_index_on_start_no_underflow() {
    let mut position = BoundPosition::Start(8);

    assert!(!position.sub_interval_index(3));
    assert_eq!(position, BoundPosition::Start(5));
}

#[test]
fn sub_bounds_index_on_start_underflow() {
    let mut position = BoundPosition::Start(8);

    assert!(position.sub_interval_index(9));
    assert_eq!(position, BoundPosition::MIN);
}

#[test]
fn sub_bounds_index_on_end_no_underflow() {
    let mut position = BoundPosition::End(8);

    assert!(!position.sub_interval_index(3));
    assert_eq!(position, BoundPosition::End(5));
}

#[test]
fn sub_bounds_index_on_end_underflow() {
    let mut position = BoundPosition::End(8);

    assert!(position.sub_interval_index(9));
    assert_eq!(position, BoundPosition::MIN);
}

#[test]
fn increment_bounds_index_start_no_overflow() {
    let mut position = BoundPosition::Start(8);

    assert!(!position.increment_interval_index());
    assert_eq!(position, BoundPosition::Start(9));
}

#[test]
fn increment_bounds_index_start_overflow() {
    let mut position = BoundPosition::Start(usize::MAX);

    assert!(position.increment_interval_index());
    assert_eq!(position, BoundPosition::MAX);
}

#[test]
fn increment_bounds_index_end_no_overflow() {
    let mut position = BoundPosition::End(8);

    assert!(!position.increment_interval_index());
    assert_eq!(position, BoundPosition::End(9));
}

#[test]
fn increment_bounds_index_end_overflow() {
    let mut position = BoundPosition::End(usize::MAX);

    assert!(position.increment_interval_index());
    assert_eq!(position, BoundPosition::MAX);
}

#[test]
fn decrement_bounds_index_start_no_underflow() {
    let mut position = BoundPosition::Start(6);

    assert!(!position.decrement_interval_index());
    assert_eq!(position, BoundPosition::Start(5));
}

#[test]
fn decrement_bounds_index_start_underflow() {
    let mut position = BoundPosition::Start(usize::MIN);

    assert!(position.decrement_interval_index());
    assert_eq!(position, BoundPosition::MIN);
}

#[test]
fn decrement_bounds_index_end_no_underflow() {
    let mut position = BoundPosition::End(6);

    assert!(!position.decrement_interval_index());
    assert_eq!(position, BoundPosition::End(5));
}

#[test]
fn decrement_bounds_index_end_underflow() {
    let mut position = BoundPosition::End(usize::MIN);

    assert!(position.decrement_interval_index());
    assert_eq!(position, BoundPosition::MIN);
}

#[test]
fn advance_by_8_start_no_overflow() {
    let mut position = BoundPosition::Start(5);

    assert!(!position.advance_by(8));
    assert_eq!(position, BoundPosition::Start(9));
}

#[test]
fn advance_by_7_start_no_overflow() {
    let mut position = BoundPosition::Start(5);

    assert!(!position.advance_by(7));
    assert_eq!(position, BoundPosition::End(8));
}

#[test]
fn advance_by_start_overflow() {
    let mut position = BoundPosition::Start(5);

    assert!(!position.advance_by(usize::MAX));
    assert!(position.advance_by(usize::MAX));
    assert_eq!(position, BoundPosition::MAX);
}

#[test]
fn advance_by_8_end_no_overflow() {
    let mut position = BoundPosition::End(5);

    assert!(!position.advance_by(8));
    assert_eq!(position, BoundPosition::End(9));
}

#[test]
fn advance_by_7_end_no_overflow() {
    let mut position = BoundPosition::End(5);

    assert!(!position.advance_by(7));
    assert_eq!(position, BoundPosition::Start(9));
}

#[test]
fn advance_by_end_overflow() {
    let mut position = BoundPosition::End(5);

    assert!(!position.advance_by(usize::MAX));
    assert!(position.advance_by(usize::MAX));
    assert_eq!(position, BoundPosition::MAX);
}

#[test]
fn advance_back_by_8_start_no_underflow() {
    let mut position = BoundPosition::Start(10);

    assert!(!position.advance_back_by(8));
    assert_eq!(position, BoundPosition::Start(6));
}

#[test]
fn advance_back_by_7_start_no_underflow() {
    let mut position = BoundPosition::Start(10);

    assert!(!position.advance_back_by(7));
    assert_eq!(position, BoundPosition::End(6));
}

#[test]
fn advance_back_by_start_underflow() {
    let mut position = BoundPosition::Start(10);

    assert!(position.advance_back_by(30));
    assert_eq!(position, BoundPosition::MIN);
}

#[test]
fn advance_back_by_8_end_no_underflow() {
    let mut position = BoundPosition::End(10);

    assert!(!position.advance_back_by(8));
    assert_eq!(position, BoundPosition::End(6));
}

#[test]
fn advance_back_by_7_end_no_underflow() {
    let mut position = BoundPosition::End(10);

    assert!(!position.advance_back_by(7));
    assert_eq!(position, BoundPosition::Start(7));
}

#[test]
fn advance_back_by_end_underflow() {
    let mut position = BoundPosition::End(10);

    assert!(position.advance_back_by(30));
    assert_eq!(position, BoundPosition::MIN);
}

#[test]
fn next_bound_start_no_overflow() {
    let mut position = BoundPosition::Start(5);

    assert!(!position.next_bound());
    assert_eq!(position, BoundPosition::End(5));
}

#[test]
fn next_bound_start_at_usize_max() {
    let mut position = BoundPosition::Start(usize::MAX);

    assert!(!position.next_bound());
    assert_eq!(position, BoundPosition::End(usize::MAX));
}

#[test]
fn next_bound_end_no_overflow() {
    let mut position = BoundPosition::End(5);

    assert!(!position.next_bound());
    assert_eq!(position, BoundPosition::Start(6));
}

#[test]
fn next_bound_end_overflow() {
    let mut position = BoundPosition::End(usize::MAX);

    assert!(position.next_bound());
    assert_eq!(position, BoundPosition::MAX);
}

#[test]
fn prev_bound_start_no_underflow() {
    let mut position = BoundPosition::Start(5);

    assert!(!position.prev_bound());
    assert_eq!(position, BoundPosition::End(4));
}

#[test]
fn prev_bound_start_underflow() {
    let mut position = BoundPosition::Start(usize::MIN);

    assert!(position.prev_bound());
    assert_eq!(position, BoundPosition::MIN);
}

#[test]
fn prev_bound_end_no_underflow() {
    let mut position = BoundPosition::End(5);

    assert!(!position.prev_bound());
    assert_eq!(position, BoundPosition::Start(5));
}

#[test]
fn prev_bound_end_usize_min_no_underflow() {
    let mut position = BoundPosition::End(usize::MIN);

    assert!(!position.prev_bound());
    assert_eq!(position, BoundPosition::Start(usize::MIN));
}

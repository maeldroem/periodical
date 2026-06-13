//! Test data for interval overlap

use std::collections::HashMap;
use std::sync::LazyLock;

use jiff::SignedDuration;

use crate::intervals::absolute::{AbsBoundPair, AbsEndBound, AbsFiniteBoundPos, AbsStartBound, EmptiableAbsBoundPair};
use crate::intervals::meta::{BoundInclusivity, IntervalType, OpeningDirection};
use crate::intervals::relative::{EmptiableRelBoundPair, RelBoundPair, RelEndBound, RelFiniteBoundPos, RelStartBound};
use crate::test_data::{BinOpMap, BinOpPair, bin_op_map, date_timestamp};

type IntervalTypeToDataMap<T> = HashMap<(IntervalType, IntervalType), &'static BinOpMap<T, T>>;

pub static ABS_DATA: LazyLock<IntervalTypeToDataMap<AbsBoundPair>> = LazyLock::new(|| {
    HashMap::from([
        (
            (IntervalType::Bounded, IntervalType::Bounded),
            LazyLock::force(&BOUNDED_BOUNDED_ABS),
        ),
        (
            (
                IntervalType::Bounded,
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
            ),
            LazyLock::force(&BOUNDED_HALF_BOUNDED_TO_FUTURE_ABS),
        ),
        (
            (
                IntervalType::Bounded,
                IntervalType::HalfBounded(OpeningDirection::ToPast),
            ),
            LazyLock::force(&BOUNDED_HALF_BOUNDED_TO_PAST_ABS),
        ),
        (
            (IntervalType::Bounded, IntervalType::Unbounded),
            LazyLock::force(&BOUNDED_UNBOUNDED_ABS),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
                IntervalType::Bounded,
            ),
            LazyLock::force(&HALF_BOUNDED_TO_FUTURE_BOUNDED_ABS),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
            ),
            LazyLock::force(&HALF_BOUNDED_TO_FUTURE_HALF_BOUNDED_TO_FUTURE_ABS),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
                IntervalType::HalfBounded(OpeningDirection::ToPast),
            ),
            LazyLock::force(&HALF_BOUNDED_TO_FUTURE_HALF_BOUNDED_TO_PAST_ABS),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
                IntervalType::Unbounded,
            ),
            LazyLock::force(&HALF_BOUNDED_TO_FUTURE_UNBOUNDED_ABS),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToPast),
                IntervalType::Bounded,
            ),
            LazyLock::force(&HALF_BOUNDED_TO_PAST_BOUNDED_ABS),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToPast),
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
            ),
            LazyLock::force(&HALF_BOUNDED_TO_PAST_HALF_BOUNDED_TO_FUTURE_ABS),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToPast),
                IntervalType::HalfBounded(OpeningDirection::ToPast),
            ),
            LazyLock::force(&HALF_BOUNDED_TO_PAST_HALF_BOUNDED_TO_PAST_ABS),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToPast),
                IntervalType::Unbounded,
            ),
            LazyLock::force(&HALF_BOUNDED_TO_PAST_UNBOUNDED_ABS),
        ),
        (
            (IntervalType::Unbounded, IntervalType::Bounded),
            LazyLock::force(&UNBOUNDED_BOUNDED_ABS),
        ),
        (
            (
                IntervalType::Unbounded,
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
            ),
            LazyLock::force(&UNBOUNDED_HALF_BOUNDED_TO_FUTURE_ABS),
        ),
        (
            (
                IntervalType::Unbounded,
                IntervalType::HalfBounded(OpeningDirection::ToPast),
            ),
            LazyLock::force(&UNBOUNDED_HALF_BOUNDED_TO_PAST_ABS),
        ),
        (
            (IntervalType::Unbounded, IntervalType::Unbounded),
            LazyLock::force(&UNBOUNDED_UNBOUNDED_ABS),
        ),
    ])
});

pub static ABS_NONEMPTY_EMPTY_DATA: LazyLock<BinOpMap<AbsBoundPair, EmptiableAbsBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "bounded_outside" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            EmptiableAbsBoundPair::Empty,
        ),
        "half_bounded_to_future_outside" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
            EmptiableAbsBoundPair::Empty,
        ),
        "half_bounded_to_past_outside" => (
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
            ),
            EmptiableAbsBoundPair::Empty,
        ),
        "unbounded_outside" => (
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
            EmptiableAbsBoundPair::Empty,
        ),
    )
});

pub static ABS_EMPTY_NONEMPTY_DATA: LazyLock<BinOpMap<EmptiableAbsBoundPair, AbsBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "bounded_outside" => (
            EmptiableAbsBoundPair::Empty,
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "half_bounded_to_future_outside" => (
            EmptiableAbsBoundPair::Empty,
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
        ),
        "half_bounded_to_past_outside" => (
            EmptiableAbsBoundPair::Empty,
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
            ),
        ),
        "unbounded_outside" => (
            EmptiableAbsBoundPair::Empty,
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
        ),
    )
});

pub static ABS_EMPTY_EMPTY_DATA: LazyLock<BinOpPair<EmptiableAbsBoundPair, EmptiableAbsBoundPair>> =
    LazyLock::new(|| BinOpPair::new(EmptiableAbsBoundPair::Empty, EmptiableAbsBoundPair::Empty));

pub static REL_DATA: LazyLock<IntervalTypeToDataMap<RelBoundPair>> = LazyLock::new(|| {
    HashMap::from([
        (
            (IntervalType::Bounded, IntervalType::Bounded),
            LazyLock::force(&BOUNDED_BOUNDED_REL),
        ),
        (
            (
                IntervalType::Bounded,
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
            ),
            LazyLock::force(&BOUNDED_HALF_BOUNDED_TO_FUTURE_REL),
        ),
        (
            (
                IntervalType::Bounded,
                IntervalType::HalfBounded(OpeningDirection::ToPast),
            ),
            LazyLock::force(&BOUNDED_HALF_BOUNDED_TO_PAST_REL),
        ),
        (
            (IntervalType::Bounded, IntervalType::Unbounded),
            LazyLock::force(&BOUNDED_UNBOUNDED_REL),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
                IntervalType::Bounded,
            ),
            LazyLock::force(&HALF_BOUNDED_TO_FUTURE_BOUNDED_REL),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
            ),
            LazyLock::force(&HALF_BOUNDED_TO_FUTURE_HALF_BOUNDED_TO_FUTURE_REL),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
                IntervalType::HalfBounded(OpeningDirection::ToPast),
            ),
            LazyLock::force(&HALF_BOUNDED_TO_FUTURE_HALF_BOUNDED_TO_PAST_REL),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
                IntervalType::Unbounded,
            ),
            LazyLock::force(&HALF_BOUNDED_TO_FUTURE_UNBOUNDED_REL),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToPast),
                IntervalType::Bounded,
            ),
            LazyLock::force(&HALF_BOUNDED_TO_PAST_BOUNDED_REL),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToPast),
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
            ),
            LazyLock::force(&HALF_BOUNDED_TO_PAST_HALF_BOUNDED_TO_FUTURE_REL),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToPast),
                IntervalType::HalfBounded(OpeningDirection::ToPast),
            ),
            LazyLock::force(&HALF_BOUNDED_TO_PAST_HALF_BOUNDED_TO_PAST_REL),
        ),
        (
            (
                IntervalType::HalfBounded(OpeningDirection::ToPast),
                IntervalType::Unbounded,
            ),
            LazyLock::force(&HALF_BOUNDED_TO_PAST_UNBOUNDED_REL),
        ),
        (
            (IntervalType::Unbounded, IntervalType::Bounded),
            LazyLock::force(&UNBOUNDED_BOUNDED_REL),
        ),
        (
            (
                IntervalType::Unbounded,
                IntervalType::HalfBounded(OpeningDirection::ToFuture),
            ),
            LazyLock::force(&UNBOUNDED_HALF_BOUNDED_TO_FUTURE_REL),
        ),
        (
            (
                IntervalType::Unbounded,
                IntervalType::HalfBounded(OpeningDirection::ToPast),
            ),
            LazyLock::force(&UNBOUNDED_HALF_BOUNDED_TO_PAST_REL),
        ),
        (
            (IntervalType::Unbounded, IntervalType::Unbounded),
            LazyLock::force(&UNBOUNDED_UNBOUNDED_REL),
        ),
    ])
});

pub static REL_NONEMPTY_EMPTY_DATA: LazyLock<BinOpMap<RelBoundPair, EmptiableRelBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "bounded_outside" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            EmptiableRelBoundPair::Empty,
        ),
        "half_bounded_to_future_outside" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
            EmptiableRelBoundPair::Empty,
        ),
        "half_bounded_to_past_outside" => (
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
            ),
            EmptiableRelBoundPair::Empty,
        ),
        "unbounded_outside" => (
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
            EmptiableRelBoundPair::Empty,
        ),
    )
});

pub static REL_EMPTY_NONEMPTY_DATA: LazyLock<BinOpMap<EmptiableRelBoundPair, RelBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "bounded_outside" => (
            EmptiableRelBoundPair::Empty,
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "half_bounded_to_future_outside" => (
            EmptiableRelBoundPair::Empty,
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
        ),
        "half_bounded_to_past_outside" => (
            EmptiableRelBoundPair::Empty,
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
            ),
        ),
        "unbounded_outside" => (
            EmptiableRelBoundPair::Empty,
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
        ),
    )
});

pub static REL_EMPTY_EMPTY_DATA: LazyLock<BinOpPair<EmptiableRelBoundPair, EmptiableRelBoundPair>> =
    LazyLock::new(|| BinOpPair::new(EmptiableRelBoundPair::Empty, EmptiableRelBoundPair::Empty));

static BOUNDED_BOUNDED_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "outside_before" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 4)).to_end_bound(),
            ),
        ),
        "outside_after" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 4)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "ends_on_start_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "ends_on_start_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "ends_on_start_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "ends_on_start_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "starts_on_end_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "starts_on_end_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "starts_on_end_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "starts_on_end_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "crosses_start" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 4)).to_end_bound(),
            ),
        ),
        "crosses_end" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 4)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "inside" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 4)).to_end_bound(),
            ),
        ),
        "inside_and_same_start_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "inside_and_same_start_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "inside_and_same_start_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "inside_and_same_start_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "inside_and_same_end_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "inside_and_same_end_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "inside_and_same_end_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "inside_and_same_end_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_incl_incl_end_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "equal_start_incl_incl_end_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_incl_incl_end_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "equal_start_incl_incl_end_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_incl_excl_end_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "equal_start_incl_excl_end_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_incl_excl_end_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "equal_start_incl_excl_end_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_excl_incl_end_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "equal_start_excl_incl_end_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_excl_incl_end_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "equal_start_excl_incl_end_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_excl_excl_end_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "equal_start_excl_excl_end_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_excl_excl_end_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "equal_start_excl_excl_end_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "contains_and_same_start_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "contains_and_same_start_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "contains_and_same_start_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "contains_and_same_start_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "contains_and_same_end_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "contains_and_same_end_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "contains_and_same_end_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "contains_and_same_end_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "contains" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 4)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
    )
});

static BOUNDED_HALF_BOUNDED_TO_FUTURE_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "outside_before" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
        ),
        "ends_on_start_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
        ),
        "ends_on_start_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
        ),
        "ends_on_start_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
        ),
        "ends_on_start_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
        ),
        "crosses_start" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
        ),
        "inside" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
        ),
        "inside_and_same_start_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
        ),
        "inside_and_same_start_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
        ),
        "inside_and_same_start_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
        ),
        "inside_and_same_start_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
        ),
    )
});

static BOUNDED_HALF_BOUNDED_TO_PAST_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "outside_after" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
            ),
        ),
        "starts_on_end_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
            ),
        ),
        "starts_on_end_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "starts_on_end_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
            ),
        ),
        "starts_on_end_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "crosses_end" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "inside" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "inside_and_same_end_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "inside_and_same_end_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "inside_and_same_end_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "inside_and_same_end_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
    )
});

static BOUNDED_UNBOUNDED_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "inside" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
        ),
    )
});

static HALF_BOUNDED_TO_FUTURE_BOUNDED_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "outside_after" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "starts_on_end_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "starts_on_end_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "starts_on_end_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "starts_on_end_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "crosses_end" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "contains_and_same_start_incl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "contains_and_same_start_incl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "contains_and_same_start_excl_incl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "contains_and_same_start_excl_excl" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "contains" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
    )
});

static HALF_BOUNDED_TO_FUTURE_HALF_BOUNDED_TO_FUTURE_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> =
    LazyLock::new(|| {
        bin_op_map!(
            "inside_and_same_end" => (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
            "equal_incl_incl" => (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
            "equal_incl_excl" => (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
            "equal_excl_incl" => (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
            "equal_excl_excl" => (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
            "contains_and_same_end" => (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        )
    });

static HALF_BOUNDED_TO_FUTURE_HALF_BOUNDED_TO_PAST_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> =
    LazyLock::new(|| {
        bin_op_map!(
            "outside_after" => (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                ),
            ),
            "starts_on_end_incl_incl" => (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                ),
            ),
            "starts_on_end_incl_excl" => (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
            "starts_on_end_excl_incl" => (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                ),
            ),
            "starts_on_end_excl_excl" => (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
            "crosses_end" => (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                ),
            ),
        )
    });

static HALF_BOUNDED_TO_FUTURE_UNBOUNDED_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "inside_and_same_end" => (
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
        ),
    )
});

static HALF_BOUNDED_TO_PAST_BOUNDED_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "outside_before" => (
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "ends_on_start_incl_incl" => (
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "ends_on_start_incl_excl" => (
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "ends_on_start_excl_incl" => (
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "ends_on_start_excl_excl" => (
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "crosses_start" => (
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
        ),
        "contains_and_same_end_incl_incl" => (
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "contains_and_same_end_incl_excl" => (
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "contains_and_same_end_excl_incl" => (
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
        "contains_and_same_end_excl_excl" => (
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "contains" => (
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
    )
});

static HALF_BOUNDED_TO_PAST_HALF_BOUNDED_TO_FUTURE_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> =
    LazyLock::new(|| {
        bin_op_map!(
            "outside_before" => (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
            "ends_on_start_incl_incl" => (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
            "ends_on_start_incl_excl" => (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
            "ends_on_start_excl_incl" => (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
            "ends_on_start_excl_excl" => (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
            "crosses_start" => (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        )
    });

static HALF_BOUNDED_TO_PAST_HALF_BOUNDED_TO_PAST_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> =
    LazyLock::new(|| {
        bin_op_map!(
            "inside_and_same_start" => (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                ),
            ),
            "equal_incl_incl" => (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                ),
            ),
            "equal_incl_excl" => (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
            "equal_excl_incl" => (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                ),
            ),
            "equal_excl_excl" => (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        date_timestamp(2026, 1, 1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
            "contains_and_same_start" => (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                ),
            ),
        )
    });

static HALF_BOUNDED_TO_PAST_UNBOUNDED_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "inside_and_same_start" => (
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
            ),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
        ),
    )
});

static UNBOUNDED_BOUNDED_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "contains" => (
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            ),
        ),
    )
});

static UNBOUNDED_HALF_BOUNDED_TO_FUTURE_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "contains_and_same_end" => (
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
        ),
    )
});

static UNBOUNDED_HALF_BOUNDED_TO_PAST_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "contains_and_same_start" => (
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
            ),
        ),
    )
});

static UNBOUNDED_UNBOUNDED_ABS: LazyLock<BinOpMap<AbsBoundPair, AbsBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "equal" => (
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture),
        )
    )
});

static BOUNDED_BOUNDED_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "outside_before" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_end_bound(),
            ),
        ),
        "outside_after" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "ends_on_start_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "ends_on_start_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "ends_on_start_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "ends_on_start_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "starts_on_end_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "starts_on_end_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "starts_on_end_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "starts_on_end_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "crosses_start" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_end_bound(),
            ),
        ),
        "crosses_end" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "inside" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_end_bound(),
            ),
        ),
        "inside_and_same_start_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "inside_and_same_start_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "inside_and_same_start_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "inside_and_same_start_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "inside_and_same_end_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "inside_and_same_end_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "inside_and_same_end_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "inside_and_same_end_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_incl_incl_end_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "equal_start_incl_incl_end_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_incl_incl_end_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "equal_start_incl_incl_end_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_incl_excl_end_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "equal_start_incl_excl_end_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_incl_excl_end_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "equal_start_incl_excl_end_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_excl_incl_end_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "equal_start_excl_incl_end_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_excl_incl_end_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "equal_start_excl_incl_end_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_excl_excl_end_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "equal_start_excl_excl_end_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "equal_start_excl_excl_end_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "equal_start_excl_excl_end_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "contains_and_same_start_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "contains_and_same_start_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "contains_and_same_start_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "contains_and_same_start_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "contains_and_same_end_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "contains_and_same_end_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "contains_and_same_end_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "contains_and_same_end_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(3),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "contains" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
    )
});

static BOUNDED_HALF_BOUNDED_TO_FUTURE_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "outside_before" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
        ),
        "ends_on_start_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
        ),
        "ends_on_start_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
        ),
        "ends_on_start_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
        ),
        "ends_on_start_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
        ),
        "crosses_start" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
        ),
        "inside" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
        ),
        "inside_and_same_start_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
        ),
        "inside_and_same_start_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
        ),
        "inside_and_same_start_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
        ),
        "inside_and_same_start_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
        ),
    )
});

static BOUNDED_HALF_BOUNDED_TO_PAST_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "outside_after" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
            ),
        ),
        "starts_on_end_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
            ),
        ),
        "starts_on_end_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "starts_on_end_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
            ),
        ),
        "starts_on_end_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "crosses_end" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "inside" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "inside_and_same_end_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "inside_and_same_end_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "inside_and_same_end_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "inside_and_same_end_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
    )
});

static BOUNDED_UNBOUNDED_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "inside" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
        ),
    )
});

static HALF_BOUNDED_TO_FUTURE_BOUNDED_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "outside_after" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "starts_on_end_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "starts_on_end_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "starts_on_end_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "starts_on_end_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "crosses_end" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "contains_and_same_start_incl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "contains_and_same_start_incl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "contains_and_same_start_excl_incl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "contains_and_same_start_excl_excl" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "contains" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
    )
});

static HALF_BOUNDED_TO_FUTURE_HALF_BOUNDED_TO_FUTURE_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> =
    LazyLock::new(|| {
        bin_op_map!(
            "inside_and_same_end" => (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
            "equal_incl_incl" => (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
            "equal_incl_excl" => (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
            "equal_excl_incl" => (
                RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
            "equal_excl_excl" => (
                RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
            "contains_and_same_end" => (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
        )
    });

static HALF_BOUNDED_TO_FUTURE_HALF_BOUNDED_TO_PAST_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> =
    LazyLock::new(|| {
        bin_op_map!(
            "outside_after" => (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
            "starts_on_end_incl_incl" => (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
            "starts_on_end_incl_excl" => (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
            "starts_on_end_excl_incl" => (
                RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
            "starts_on_end_excl_excl" => (
                RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
            "crosses_end" => (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        )
    });

static HALF_BOUNDED_TO_FUTURE_UNBOUNDED_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "inside_and_same_end" => (
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
        ),
    )
});

static HALF_BOUNDED_TO_PAST_BOUNDED_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "outside_before" => (
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "ends_on_start_incl_incl" => (
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "ends_on_start_incl_excl" => (
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "ends_on_start_excl_incl" => (
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "ends_on_start_excl_excl" => (
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "crosses_start" => (
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
        ),
        "contains_and_same_end_incl_incl" => (
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "contains_and_same_end_incl_excl" => (
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "contains_and_same_end_excl_incl" => (
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
        "contains_and_same_end_excl_excl" => (
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(2),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ),
        ),
        "contains" => (
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            ),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
    )
});

static HALF_BOUNDED_TO_PAST_HALF_BOUNDED_TO_FUTURE_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> =
    LazyLock::new(|| {
        bin_op_map!(
            "outside_before" => (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
            "ends_on_start_incl_incl" => (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
            "ends_on_start_incl_excl" => (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
            "ends_on_start_excl_incl" => (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
            "ends_on_start_excl_excl" => (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
            "crosses_start" => (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
        )
    });

static HALF_BOUNDED_TO_PAST_HALF_BOUNDED_TO_PAST_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> =
    LazyLock::new(|| {
        bin_op_map!(
            "inside_and_same_start" => (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
            "equal_incl_incl" => (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
            "equal_incl_excl" => (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
            "equal_excl_incl" => (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
            "equal_excl_excl" => (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new_with_incl(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
            "contains_and_same_start" => (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        )
    });

static HALF_BOUNDED_TO_PAST_UNBOUNDED_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "inside_and_same_start" => (
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
            ),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
        ),
    )
});

static UNBOUNDED_BOUNDED_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "contains" => (
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            ),
        ),
    )
});

static UNBOUNDED_HALF_BOUNDED_TO_FUTURE_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "contains_and_same_end" => (
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
            RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            ),
        ),
    )
});

static UNBOUNDED_HALF_BOUNDED_TO_PAST_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "contains_and_same_start" => (
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
            RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
            ),
        ),
    )
});

static UNBOUNDED_UNBOUNDED_REL: LazyLock<BinOpMap<RelBoundPair, RelBoundPair>> = LazyLock::new(|| {
    bin_op_map!(
        "equal" => (
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
            RelBoundPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture),
        )
    )
});

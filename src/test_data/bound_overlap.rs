//! Test data for bound overlap

use std::sync::LazyLock;

use jiff::SignedDuration;

use crate::intervals::absolute::{
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsFiniteEndBound,
    AbsFiniteStartBound,
    AbsStartBound,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{
    RelEndBound,
    RelFiniteBoundPos,
    RelFiniteEndBound,
    RelFiniteStartBound,
    RelStartBound,
};
use crate::test_data::{BinOpMap, BinOpPair, bin_op_map, date_timestamp};

pub static FINITE_START_FINITE_START_ABS: LazyLock<BinOpMap<AbsFiniteStartBound, AbsFiniteStartBound>> =
    LazyLock::new(|| {
        bin_op_map!(
            "before" => (
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound(),
            ),
            "equal_incl_incl" => (
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
            ),
            "equal_incl_excl" => (
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                ).to_finite_start_bound(),
            ),
            "equal_excl_incl" => (
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                ).to_finite_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
            ),
            "equal_excl_excl" => (
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                ).to_finite_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                ).to_finite_start_bound(),
            ),
            "after" => (
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
            ),
        )
    });

pub static FINITE_START_INF_START_ABS: LazyLock<Result<BinOpPair<AbsFiniteStartBound, AbsStartBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
            AbsStartBound::InfinitePast,
        ))
    });

pub static INF_START_FINITE_START_ABS: LazyLock<Result<BinOpPair<AbsStartBound, AbsFiniteStartBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
        ))
    });

pub static INF_START_INF_START_ABS: LazyLock<Result<BinOpPair<AbsStartBound, AbsStartBound>, jiff::Error>> =
    LazyLock::new(|| Ok(BinOpPair::new(AbsStartBound::InfinitePast, AbsStartBound::InfinitePast)));

pub static FINITE_START_FINITE_END_ABS: LazyLock<BinOpMap<AbsFiniteStartBound, AbsFiniteEndBound>> =
    LazyLock::new(|| {
        bin_op_map!(
            "before" => (
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound(),
            ),
            "equal_incl_incl" => (
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
            ),
            "equal_incl_excl" => (
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                ).to_finite_end_bound(),
            ),
            "equal_excl_incl" => (
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                ).to_finite_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
            ),
            "equal_excl_excl" => (
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                ).to_finite_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    date_timestamp(2026, 1, 1),
                    BoundInclusivity::Exclusive,
                ).to_finite_end_bound(),
            ),
            "after" => (
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
            ),
        )
    });

pub static FINITE_START_INF_END_ABS: LazyLock<Result<BinOpPair<AbsFiniteStartBound, AbsEndBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
            AbsEndBound::InfiniteFuture,
        ))
    });

pub static INF_START_FINITE_END_ABS: LazyLock<Result<BinOpPair<AbsStartBound, AbsFiniteEndBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            AbsStartBound::InfinitePast,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
        ))
    });

pub static INF_START_INF_END_ABS: LazyLock<Result<BinOpPair<AbsStartBound, AbsEndBound>, jiff::Error>> =
    LazyLock::new(|| Ok(BinOpPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture)));

static FINITE_END_FINITE_START_ABS: LazyLock<BinOpMap<AbsFiniteEndBound, AbsFiniteStartBound>> = LazyLock::new(|| {
    bin_op_map!(
        "before" => (
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_start_bound(),
        ),
        "equal_incl_incl" => (
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
        ),
        "equal_incl_excl" => (
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
            AbsFiniteBoundPos::new_with_incl(
                date_timestamp(2026, 1, 1),
                BoundInclusivity::Exclusive,
            ).to_finite_start_bound(),
        ),
        "equal_excl_incl" => (
            AbsFiniteBoundPos::new_with_incl(
                date_timestamp(2026, 1, 1),
                BoundInclusivity::Exclusive,
            ).to_finite_end_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
        ),
        "equal_excl_excl" => (
            AbsFiniteBoundPos::new_with_incl(
                date_timestamp(2026, 1, 1),
                BoundInclusivity::Exclusive,
            ).to_finite_end_bound(),
            AbsFiniteBoundPos::new_with_incl(
                date_timestamp(2026, 1, 1),
                BoundInclusivity::Exclusive,
            ).to_finite_start_bound(),
        ),
        "after" => (
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
        ),
    )
});

pub static FINITE_END_INF_START_ABS: LazyLock<Result<BinOpPair<AbsFiniteEndBound, AbsStartBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
            AbsStartBound::InfinitePast,
        ))
    });

pub static INF_END_FINITE_START_ABS: LazyLock<Result<BinOpPair<AbsEndBound, AbsFiniteStartBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            AbsEndBound::InfiniteFuture,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_start_bound(),
        ))
    });

pub static INF_END_INF_START_ABS: LazyLock<Result<BinOpPair<AbsEndBound, AbsStartBound>, jiff::Error>> =
    LazyLock::new(|| Ok(BinOpPair::new(AbsEndBound::InfiniteFuture, AbsStartBound::InfinitePast)));

pub static FINITE_END_FINITE_END_ABS: LazyLock<BinOpMap<AbsFiniteEndBound, AbsFiniteEndBound>> = LazyLock::new(|| {
    bin_op_map!(
        "before" => (
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound(),
        ),
        "equal_incl_incl" => (
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
        ),
        "equal_incl_excl" => (
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
            AbsFiniteBoundPos::new_with_incl(
                date_timestamp(2026, 1, 1),
                BoundInclusivity::Exclusive,
            ).to_finite_end_bound(),
        ),
        "equal_excl_incl" => (
            AbsFiniteBoundPos::new_with_incl(
                date_timestamp(2026, 1, 1),
                BoundInclusivity::Exclusive,
            ).to_finite_end_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
        ),
        "equal_excl_excl" => (
            AbsFiniteBoundPos::new_with_incl(
                date_timestamp(2026, 1, 1),
                BoundInclusivity::Exclusive,
            ).to_finite_end_bound(),
            AbsFiniteBoundPos::new_with_incl(
                date_timestamp(2026, 1, 1),
                BoundInclusivity::Exclusive,
            ).to_finite_end_bound(),
        ),
        "after" => (
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_finite_end_bound(),
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
        ),
    )
});

pub static FINITE_END_INF_END_ABS: LazyLock<Result<BinOpPair<AbsFiniteEndBound, AbsEndBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
            AbsEndBound::InfiniteFuture,
        ))
    });

pub static INF_END_FINITE_END_ABS: LazyLock<Result<BinOpPair<AbsEndBound, AbsFiniteEndBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            AbsEndBound::InfiniteFuture,
            AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_finite_end_bound(),
        ))
    });

pub static INF_END_INF_END_ABS: LazyLock<Result<BinOpPair<AbsEndBound, AbsEndBound>, jiff::Error>> =
    LazyLock::new(|| Ok(BinOpPair::new(AbsEndBound::InfiniteFuture, AbsEndBound::InfiniteFuture)));

pub static FINITE_START_FINITE_START_REL: LazyLock<BinOpMap<RelFiniteStartBound, RelFiniteStartBound>> =
    LazyLock::new(|| {
        bin_op_map!(
            "before" => (
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound(),
            ),
            "equal_incl_incl" => (
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
            ),
            "equal_incl_excl" => (
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                ).to_finite_start_bound(),
            ),
            "equal_excl_incl" => (
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                ).to_finite_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
            ),
            "equal_excl_excl" => (
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                ).to_finite_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                ).to_finite_start_bound(),
            ),
            "after" => (
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
            ),
        )
    });

pub static FINITE_START_INF_START_REL: LazyLock<Result<BinOpPair<RelFiniteStartBound, RelStartBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
            RelStartBound::InfinitePast,
        ))
    });

pub static INF_START_FINITE_START_REL: LazyLock<Result<BinOpPair<RelStartBound, RelFiniteStartBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
        ))
    });

pub static INF_START_INF_START_REL: LazyLock<Result<BinOpPair<RelStartBound, RelStartBound>, jiff::Error>> =
    LazyLock::new(|| Ok(BinOpPair::new(RelStartBound::InfinitePast, RelStartBound::InfinitePast)));

pub static FINITE_START_FINITE_END_REL: LazyLock<BinOpMap<RelFiniteStartBound, RelFiniteEndBound>> =
    LazyLock::new(|| {
        bin_op_map!(
            "before" => (
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound(),
            ),
            "equal_incl_incl" => (
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
            ),
            "equal_incl_excl" => (
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                ).to_finite_end_bound(),
            ),
            "equal_excl_incl" => (
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                ).to_finite_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
            ),
            "equal_excl_excl" => (
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                ).to_finite_start_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                ).to_finite_end_bound(),
            ),
            "after" => (
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
            ),
        )
    });

pub static FINITE_START_INF_END_REL: LazyLock<Result<BinOpPair<RelFiniteStartBound, RelEndBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
            RelEndBound::InfiniteFuture,
        ))
    });

pub static INF_START_FINITE_END_REL: LazyLock<Result<BinOpPair<RelStartBound, RelFiniteEndBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
        ))
    });

pub static INF_START_INF_END_REL: LazyLock<Result<BinOpPair<RelStartBound, RelEndBound>, jiff::Error>> =
    LazyLock::new(|| Ok(BinOpPair::new(RelStartBound::InfinitePast, RelEndBound::InfiniteFuture)));

pub static FINITE_END_FINITE_START_REL: LazyLock<BinOpMap<RelFiniteEndBound, RelFiniteStartBound>> =
    LazyLock::new(|| {
        bin_op_map!(
            "before" => (
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_start_bound(),
            ),
            "equal_incl_incl" => (
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
            ),
            "equal_incl_excl" => (
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                ).to_finite_start_bound(),
            ),
            "equal_excl_incl" => (
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                ).to_finite_end_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
            ),
            "equal_excl_excl" => (
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                ).to_finite_end_bound(),
                RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(1),
                    BoundInclusivity::Exclusive,
                ).to_finite_start_bound(),
            ),
            "after" => (
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
            ),
        )
    });

pub static FINITE_END_INF_START_REL: LazyLock<Result<BinOpPair<RelFiniteEndBound, RelStartBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
            RelStartBound::InfinitePast,
        ))
    });

pub static INF_END_FINITE_START_REL: LazyLock<Result<BinOpPair<RelEndBound, RelFiniteStartBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            RelEndBound::InfiniteFuture,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_start_bound(),
        ))
    });

pub static INF_END_INF_START_REL: LazyLock<Result<BinOpPair<RelEndBound, RelStartBound>, jiff::Error>> =
    LazyLock::new(|| Ok(BinOpPair::new(RelEndBound::InfiniteFuture, RelStartBound::InfinitePast)));

pub static FINITE_END_FINITE_END_REL: LazyLock<BinOpMap<RelFiniteEndBound, RelFiniteEndBound>> = LazyLock::new(|| {
    bin_op_map!(
        "before" => (
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound(),
        ),
        "equal_incl_incl" => (
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
        ),
        "equal_incl_excl" => (
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
            RelFiniteBoundPos::new_with_incl(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ).to_finite_end_bound(),
        ),
        "equal_excl_incl" => (
            RelFiniteBoundPos::new_with_incl(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ).to_finite_end_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
        ),
        "equal_excl_excl" => (
            RelFiniteBoundPos::new_with_incl(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ).to_finite_end_bound(),
            RelFiniteBoundPos::new_with_incl(
                SignedDuration::from_hours(1),
                BoundInclusivity::Exclusive,
            ).to_finite_end_bound(),
        ),
        "after" => (
            RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_finite_end_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
        ),
    )
});

pub static FINITE_END_INF_END_REL: LazyLock<Result<BinOpPair<RelFiniteEndBound, RelEndBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
            RelEndBound::InfiniteFuture,
        ))
    });

pub static INF_END_FINITE_END_REL: LazyLock<Result<BinOpPair<RelEndBound, RelFiniteEndBound>, jiff::Error>> =
    LazyLock::new(|| {
        Ok(BinOpPair::new(
            RelEndBound::InfiniteFuture,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_finite_end_bound(),
        ))
    });

pub static INF_END_INF_END_REL: LazyLock<Result<BinOpPair<RelEndBound, RelEndBound>, jiff::Error>> =
    LazyLock::new(|| Ok(BinOpPair::new(RelEndBound::InfiniteFuture, RelEndBound::InfiniteFuture)));

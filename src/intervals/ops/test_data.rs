use std::collections::HashMap;
use std::sync::LazyLock;

use jiff::{SignedDuration, Timestamp};

use crate::intervals::absolute::{AbsBoundPair, AbsEndBound, AbsFiniteBoundPos, AbsStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelStartBound,
};

type TestDataPairMap<T> = LazyLock<HashMap<&'static str, (T, T)>>;
type FallibleTestDataPairMap<T, E> = LazyLock<Result<HashMap<&'static str, (T, T)>, E>>;

pub static BOUNDED_BOUNDED_ABS: FallibleTestDataPairMap<AbsBoundPair, jiff::Error> = LazyLock::new(|| {
    Ok(HashMap::from([
        (
            "outside_before",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "outside_after",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_start",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_end",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_incl_end_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_incl_end_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_incl_end_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_incl_end_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_excl_end_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_excl_end_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_excl_end_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_excl_end_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_incl_end_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_incl_end_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_incl_end_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_incl_end_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_excl_end_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_excl_end_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_excl_end_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_excl_end_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "contains",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
    ]))
});

pub static BOUNDED_HALF_BOUNDED_ABS: FallibleTestDataPairMap<AbsBoundPair, jiff::Error> = LazyLock::new(|| {
    Ok(HashMap::from([
        (
            "outside_before",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "outside_after",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "starts_on_end_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_start",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "crosses_end",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_to_future",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_to_past",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
    ]))
});

pub static HALF_BOUNDED_BOUNDED_ABS: FallibleTestDataPairMap<AbsBoundPair, jiff::Error> = LazyLock::new(|| {
    Ok(HashMap::from([
        (
            "outside_before",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "outside_after",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_incl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_start",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_end",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_incl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_excl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_excl_incl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_excl_excl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "contains_to_future",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_to_past",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
    ]))
});

pub static HALF_BOUNDED_HALF_BOUNDED_ABS: FallibleTestDataPairMap<AbsBoundPair, jiff::Error> = LazyLock::new(|| {
    Ok(HashMap::from([
        (
            "outside_before",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "outside_after",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_excl_incl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "starts_on_end_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_start",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "crosses_end",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "equal_to_future_incl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "equal_to_future_incl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "equal_to_future_excl_incl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "equal_to_future_excl_excl",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "equal_to_past_incl_incl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_to_past_incl_excl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "equal_to_past_excl_incl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_to_past_excl_excl",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start",
            (
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end",
            (
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
                AbsBoundPair::new(
                    AbsFiniteBoundPos::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                ),
            ),
        ),
    ]))
});

pub static BOUNDED_BOUNDED_REL: TestDataPairMap<RelBoundPair> = LazyLock::new(|| {
    HashMap::from([
        (
            "outside_before",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
            ),
        ),
        (
            "outside_after",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
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
        ),
        (
            "ends_on_start_excl_incl",
            (
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
        ),
        (
            "ends_on_start_excl_excl",
            (
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
        ),
        (
            "starts_on_end_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
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
        ),
        (
            "starts_on_end_excl_incl",
            (
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
        ),
        (
            "starts_on_end_excl_excl",
            (
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
        ),
        (
            "crosses_start",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_end",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_excl",
            (
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
        ),
        (
            "inside_and_same_start_excl_incl",
            (
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
        ),
        (
            "inside_and_same_start_excl_excl",
            (
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
        ),
        (
            "inside_and_same_end_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_excl",
            (
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
        ),
        (
            "inside_and_same_end_excl_incl",
            (
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
        ),
        (
            "inside_and_same_end_excl_excl",
            (
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
        ),
        (
            "equal_start_incl_incl_end_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_incl_end_incl_excl",
            (
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
        ),
        (
            "equal_start_incl_incl_end_excl_incl",
            (
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
        ),
        (
            "equal_start_incl_incl_end_excl_excl",
            (
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
        ),
        (
            "equal_start_incl_excl_end_incl_incl",
            (
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
        ),
        (
            "equal_start_incl_excl_end_incl_excl",
            (
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
        ),
        (
            "equal_start_incl_excl_end_excl_incl",
            (
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
        ),
        (
            "equal_start_incl_excl_end_excl_excl",
            (
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
        ),
        (
            "equal_start_excl_incl_end_incl_incl",
            (
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
        ),
        (
            "equal_start_excl_incl_end_incl_excl",
            (
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
        ),
        (
            "equal_start_excl_incl_end_excl_incl",
            (
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
        ),
        (
            "equal_start_excl_incl_end_excl_excl",
            (
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
        ),
        (
            "equal_start_excl_excl_end_incl_incl",
            (
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
        ),
        (
            "equal_start_excl_excl_end_incl_excl",
            (
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
        ),
        (
            "equal_start_excl_excl_end_excl_incl",
            (
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
        ),
        (
            "equal_start_excl_excl_end_excl_excl",
            (
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
        ),
        (
            "contains_and_same_start_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_excl",
            (
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
        ),
        (
            "contains_and_same_start_excl_incl",
            (
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
        ),
        (
            "contains_and_same_start_excl_excl",
            (
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
        ),
        (
            "contains_and_same_end_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_excl",
            (
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
        ),
        (
            "contains_and_same_end_excl_incl",
            (
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
        ),
        (
            "contains_and_same_end_excl_excl",
            (
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
        ),
        (
            "contains",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
    ])
});

pub static BOUNDED_HALF_BOUNDED_REL: TestDataPairMap<RelBoundPair> = LazyLock::new(|| {
    HashMap::from([
        (
            "outside_before",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "outside_after",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
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
        ),
        (
            "ends_on_start_excl_incl",
            (
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
        ),
        (
            "ends_on_start_excl_excl",
            (
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
        ),
        (
            "starts_on_end_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
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
        ),
        (
            "starts_on_end_excl_incl",
            (
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
        ),
        (
            "starts_on_end_excl_excl",
            (
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
        ),
        (
            "crosses_start",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "crosses_end",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_to_future",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_to_past",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_excl",
            (
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
        ),
        (
            "inside_and_same_start_excl_incl",
            (
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
        ),
        (
            "inside_and_same_start_excl_excl",
            (
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
        ),
        (
            "inside_and_same_end_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_excl",
            (
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
        ),
        (
            "inside_and_same_end_excl_incl",
            (
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
        ),
        (
            "inside_and_same_end_excl_excl",
            (
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
        ),
    ])
});

pub static HALF_BOUNDED_BOUNDED_REL: TestDataPairMap<RelBoundPair> = LazyLock::new(|| {
    HashMap::from([
        (
            "outside_before",
            (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "outside_after",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
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
        ),
        (
            "starts_on_end_excl_incl",
            (
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
        ),
        (
            "starts_on_end_excl_excl",
            (
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
        ),
        (
            "ends_on_start_incl_incl",
            (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
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
        ),
        (
            "ends_on_start_excl_incl",
            (
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
        ),
        (
            "ends_on_start_excl_excl",
            (
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
        ),
        (
            "crosses_start",
            (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_end",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_excl",
            (
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
        ),
        (
            "contains_and_same_start_excl_incl",
            (
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
        ),
        (
            "contains_and_same_start_excl_excl",
            (
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
        ),
        (
            "contains_and_same_end_incl_incl",
            (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_excl",
            (
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
        ),
        (
            "contains_and_same_end_excl_incl",
            (
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
        ),
        (
            "contains_and_same_end_excl_excl",
            (
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
        ),
        (
            "contains_to_future",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_to_past",
            (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
    ])
});

pub static HALF_BOUNDED_HALF_BOUNDED_REL: TestDataPairMap<RelBoundPair> = LazyLock::new(|| {
    HashMap::from([
        (
            "outside_before",
            (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "outside_after",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
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
        ),
        (
            "ends_on_start_excl_incl",
            (
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
        ),
        (
            "ends_on_start_excl_excl",
            (
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
        ),
        (
            "starts_on_end_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
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
        ),
        (
            "starts_on_end_excl_incl",
            (
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
        ),
        (
            "starts_on_end_excl_excl",
            (
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
        ),
        (
            "crosses_start",
            (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "crosses_end",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start",
            (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "equal_to_future_incl_incl",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "equal_to_future_incl_excl",
            (
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
        ),
        (
            "equal_to_future_excl_incl",
            (
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
        ),
        (
            "equal_to_future_excl_excl",
            (
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
        ),
        (
            "equal_to_past_incl_incl",
            (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_to_past_incl_excl",
            (
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
        ),
        (
            "equal_to_past_excl_incl",
            (
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
        ),
        (
            "equal_to_past_excl_excl",
            (
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
        ),
        (
            "contains_and_same_start",
            (
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end",
            (
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
                RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                ),
            ),
        ),
    ])
});

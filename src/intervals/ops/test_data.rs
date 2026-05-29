use std::collections::HashMap;
use std::sync::LazyLock;

use jiff::{SignedDuration, Timestamp};

use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBoundPosition, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeBoundPair, RelativeEndBound, RelativeFiniteBoundPosition, RelativeStartBound};

type TestDataPairMap<T> = LazyLock<HashMap<&'static str, (T, T)>>;
type FallibleTestDataPairMap<T, E> = LazyLock<Result<HashMap<&'static str, (T, T)>, E>>;

pub static BOUNDED_BOUNDED_ABS: FallibleTestDataPairMap<AbsoluteBoundPair, jiff::Error> = LazyLock::new(|| {
    Ok(HashMap::from([
        (
            "outside_before",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "outside_after",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_end",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_incl_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_incl_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_excl_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_excl_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_incl_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_incl_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_excl_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_excl_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
    ]))
});

pub static BOUNDED_HALF_BOUNDED_ABS: FallibleTestDataPairMap<AbsoluteBoundPair, jiff::Error> = LazyLock::new(|| {
    Ok(HashMap::from([
        (
            "outside_before",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "outside_after",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_excl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "starts_on_end_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "crosses_end",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_to_future",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_to_past",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
    ]))
});

pub static HALF_BOUNDED_BOUNDED_ABS: FallibleTestDataPairMap<AbsoluteBoundPair, jiff::Error> = LazyLock::new(|| {
    Ok(HashMap::from([
        (
            "outside_before",
            (
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "outside_after",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_start",
            (
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_end",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_to_past",
            (
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
    ]))
});

pub static HALF_BOUNDED_HALF_BOUNDED_ABS: FallibleTestDataPairMap<AbsoluteBoundPair, jiff::Error> =
    LazyLock::new(|| {
        Ok(HashMap::from([
            (
                "outside_before",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                ),
            ),
            (
                "outside_after",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                ),
            ),
            (
                "ends_on_start_incl_incl",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                ),
            ),
            (
                "ends_on_start_incl_excl",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                ),
            ),
            (
                "ends_on_start_excl_incl",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                ),
            ),
            (
                "ends_on_start_excl_excl",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                ),
            ),
            (
                "starts_on_end_incl_incl",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                ),
            ),
            (
                "starts_on_end_incl_excl",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                ),
            ),
            (
                "starts_on_end_excl_excl",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                ),
            ),
            (
                "crosses_end",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                ),
            ),
            (
                "inside_and_same_start",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                ),
            ),
            (
                "inside_and_same_end",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                ),
            ),
            (
                "equal_to_future_incl_incl",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                ),
            ),
            (
                "equal_to_future_incl_excl",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                ),
            ),
            (
                "equal_to_future_excl_incl",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                ),
            ),
            (
                "equal_to_future_excl_excl",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                ),
            ),
            (
                "equal_to_past_incl_incl",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                ),
            ),
            (
                "equal_to_past_incl_excl",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                ),
            ),
            (
                "equal_to_past_excl_excl",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
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
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    ),
                ),
            ),
            (
                "contains_and_same_end",
                (
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    ),
                ),
            ),
        ]))
    });

pub static BOUNDED_BOUNDED_REL: TestDataPairMap<RelativeBoundPair> = LazyLock::new(|| {
    HashMap::from([
        (
            "outside_before",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
            ),
        ),
        (
            "outside_after",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_end",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_incl_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_incl_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_excl_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_excl_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_incl_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_incl_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_excl_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_excl_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
    ])
});

pub static BOUNDED_HALF_BOUNDED_REL: TestDataPairMap<RelativeBoundPair> = LazyLock::new(|| {
    HashMap::from([
        (
            "outside_before",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "outside_after",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_excl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "starts_on_end_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "crosses_end",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_to_future",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_to_past",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
    ])
});

pub static HALF_BOUNDED_BOUNDED_REL: TestDataPairMap<RelativeBoundPair> = LazyLock::new(|| {
    HashMap::from([
        (
            "outside_before",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "outside_after",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_incl",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_start",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_end",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_to_past",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
    ])
});

pub static HALF_BOUNDED_HALF_BOUNDED_REL: TestDataPairMap<RelativeBoundPair> = LazyLock::new(|| {
    HashMap::from([
        (
            "outside_before",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "outside_after",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_excl_incl",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "starts_on_end_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "crosses_end",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "equal_to_future_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "equal_to_future_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "equal_to_future_excl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "equal_to_future_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "equal_to_past_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_to_past_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_to_past_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new_with_inclusivity(
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
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
    ])
});

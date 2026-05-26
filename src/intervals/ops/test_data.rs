use std::collections::HashMap;
use std::sync::LazyLock;

use jiff::{SignedDuration, Timestamp};

use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{RelativeBoundPair, RelativeEndBound, RelativeFiniteBound, RelativeStartBound};

type TestDataPairMap<T> = LazyLock<HashMap<&'static str, (T, T)>>;
type FallibleTestDataPairMap<T, E> = LazyLock<Result<HashMap<&'static str, (T, T)>, E>>;

pub static BOUNDED_BOUNDED_ABS: FallibleTestDataPairMap<AbsoluteBoundPair, jiff::Error> = LazyLock::new(|| {
    Ok(HashMap::from([
        (
            "outside_before",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "outside_after",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_end",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_incl_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_incl_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_excl_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_excl_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_incl_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_incl_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_excl_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_excl_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-04 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
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
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "outside_after",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "crosses_end",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_to_future",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_to_past",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_incl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBound::new_with_inclusivity(
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
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_excl_excl",
            (
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
            ),
        ),
        (
            "outside_after",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
            ),
        ),
        (
            "crosses_end",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_incl_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_incl_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_excl_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_incl_excl_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_incl_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_incl_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_excl_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "equal_start_excl_excl_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_start_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "contains_and_same_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(4)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "outside_after",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "ends_on_start_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "ends_on_start_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
                ),
            ),
        ),
        (
            "starts_on_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "crosses_end",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_to_future",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_to_past",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_incl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_start_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                ),
            ),
        ),
        (
            "inside_and_same_start_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_incl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBound::new_with_inclusivity(
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
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                ),
            ),
        ),
        (
            "inside_and_same_end_excl_excl",
            (
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                ),
            ),
        ),
    ])
});

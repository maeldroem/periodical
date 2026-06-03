use std::error::Error;

use jiff::{SignedDuration, Zoned};

use super::bound_ord::*;
use crate::intervals::absolute::{AbsEndBound, AbsFiniteBoundPos, AbsStartBound};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
use crate::intervals::relative::{RelEndBound, RelFiniteBoundPos, RelStartBound};

#[test]
fn abs_start_start_less_inf_past_finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsStartBound::InfinitePast.bound_cmp(
            &AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
        ),
        BoundOrdering::Less,
    );

    Ok(())
}

#[test]
fn abs_start_start_less_finite_finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
            ),
        BoundOrdering::Less,
    );

    Ok(())
}

#[test]
fn abs_start_start_equal_inf_past() {
    assert_eq!(
        AbsStartBound::InfinitePast.bound_cmp(&AbsStartBound::InfinitePast),
        BoundOrdering::Equal(None),
    );
}

#[test]
fn abs_start_start_equal_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_start_start_equal_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_start_start_equal_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_start_bound()
        .bound_cmp(
            &AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_start_start_equal_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_start_bound()
        .bound_cmp(
            &AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_start_start_greater_finite_inf_past() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .bound_cmp(&AbsStartBound::InfinitePast),
        BoundOrdering::Greater,
    );

    Ok(())
}

#[test]
fn abs_start_start_greater_finite_finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
            ),
        BoundOrdering::Greater,
    );

    Ok(())
}

#[test]
fn abs_start_end_less_inf_past_inf_future() {
    assert_eq!(
        AbsStartBound::InfinitePast.bound_cmp(&AbsEndBound::InfiniteFuture),
        BoundOrdering::Less,
    );
}

#[test]
fn abs_start_end_less_inf_past_finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsStartBound::InfinitePast.bound_cmp(
            &AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
        ),
        BoundOrdering::Less,
    );

    Ok(())
}

#[test]
fn abs_start_end_less_finite_inf_future() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .bound_cmp(&AbsEndBound::InfiniteFuture),
        BoundOrdering::Less,
    );

    Ok(())
}

#[test]
fn abs_start_end_less_finite_finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
            ),
        BoundOrdering::Less,
    );

    Ok(())
}

#[test]
fn abs_start_end_equal_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_start_end_equal_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_start_end_equal_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_start_bound()
        .bound_cmp(
            &AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_start_end_equal_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_start_bound()
        .bound_cmp(
            &AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_start_end_greater() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_start_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
            ),
        BoundOrdering::Greater,
    );

    Ok(())
}

#[test]
fn abs_end_start_less() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_end_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
            ),
        BoundOrdering::Less,
    );

    Ok(())
}

#[test]
fn abs_end_start_equal_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_end_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_end_start_equal_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_end_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_end_start_equal_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_end_bound()
        .bound_cmp(
            &AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_end_start_equal_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_end_bound()
        .bound_cmp(
            &AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_end_start_greater_inf_future_inf_past() {
    assert_eq!(
        AbsEndBound::InfiniteFuture.bound_cmp(&AbsStartBound::InfinitePast),
        BoundOrdering::Greater,
    );
}

#[test]
fn abs_end_start_greater_inf_future_finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsEndBound::InfiniteFuture.bound_cmp(
            &AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
        ),
        BoundOrdering::Greater,
    );

    Ok(())
}

#[test]
fn abs_end_start_greater_finite_inf_past() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_end_bound()
            .bound_cmp(&AbsStartBound::InfinitePast),
        BoundOrdering::Greater,
    );

    Ok(())
}

#[test]
fn abs_end_start_greater_finite_finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_end_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
            ),
        BoundOrdering::Greater,
    );

    Ok(())
}

#[test]
fn abs_end_end_less_finite_inf_future() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_end_bound()
            .bound_cmp(&AbsEndBound::InfiniteFuture),
        BoundOrdering::Less,
    );

    Ok(())
}

#[test]
fn abs_end_end_less_finite_finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_end_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
            ),
        BoundOrdering::Less,
    );

    Ok(())
}

#[test]
fn abs_end_end_equal_inf_future_inf_future() {
    assert_eq!(
        AbsEndBound::InfiniteFuture.bound_cmp(&AbsEndBound::InfiniteFuture),
        BoundOrdering::Equal(None),
    );
}

#[test]
fn abs_end_end_equal_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_end_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_end_end_equal_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
            .to_end_bound()
            .bound_cmp(
                &AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_end_end_equal_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_end_bound()
        .bound_cmp(
            &AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );

    Ok(())
}

#[test]
fn abs_end_end_equal_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            BoundInclusivity::Exclusive,
        )
        .to_end_bound()
        .bound_cmp(
            &AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
        ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );

    Ok(())
}

#[test]
fn rel_start_start_less_inf_past_finite() {
    assert_eq!(
        RelStartBound::InfinitePast
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_start_bound()),
        BoundOrdering::Less,
    );
}

#[test]
fn rel_start_start_less_finite_finite() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_start_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(102)).to_start_bound()),
        BoundOrdering::Less,
    );
}

#[test]
fn rel_start_start_equal_inf_past() {
    assert_eq!(
        RelStartBound::InfinitePast.bound_cmp(&RelStartBound::InfinitePast),
        BoundOrdering::Equal(None),
    );
}

#[test]
fn rel_start_start_equal_inclusive_inclusive() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_start_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_start_bound()),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn rel_start_start_equal_inclusive_exclusive() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_start_bound()
            .bound_cmp(
                &RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(101),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn rel_start_start_equal_exclusive_inclusive() {
    assert_eq!(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(101), BoundInclusivity::Exclusive,)
            .to_start_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_start_bound()),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn rel_start_start_equal_exclusive_exclusive() {
    assert_eq!(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(101), BoundInclusivity::Exclusive,)
            .to_start_bound()
            .bound_cmp(
                &RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(101),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothStarts(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn rel_start_start_greater_finite_inf_past() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_start_bound()
            .bound_cmp(&RelStartBound::InfinitePast),
        BoundOrdering::Greater,
    );
}

#[test]
fn rel_start_start_greater_finite_finite() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(102))
            .to_start_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_start_bound()),
        BoundOrdering::Greater,
    );
}

#[test]
fn rel_start_end_less_inf_past_inf_future() {
    assert_eq!(
        RelStartBound::InfinitePast.bound_cmp(&RelEndBound::InfiniteFuture),
        BoundOrdering::Less,
    );
}

#[test]
fn rel_start_end_less_inf_past_finite() {
    assert_eq!(
        RelStartBound::InfinitePast
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_end_bound()),
        BoundOrdering::Less,
    );
}

#[test]
fn rel_start_end_less_finite_inf_future() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_start_bound()
            .bound_cmp(&RelEndBound::InfiniteFuture),
        BoundOrdering::Less,
    );
}

#[test]
fn rel_start_end_less_finite_finite() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_start_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(102)).to_end_bound()),
        BoundOrdering::Less,
    );
}

#[test]
fn rel_start_end_equal_inclusive_inclusive() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_start_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_end_bound()),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn rel_start_end_equal_inclusive_exclusive() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_start_bound()
            .bound_cmp(
                &RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(101),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn rel_start_end_equal_exclusive_inclusive() {
    assert_eq!(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(101), BoundInclusivity::Exclusive,)
            .to_start_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_end_bound()),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn rel_start_end_equal_exclusive_exclusive() {
    assert_eq!(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(101), BoundInclusivity::Exclusive,)
            .to_start_bound()
            .bound_cmp(
                &RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(101),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::EndStart(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn rel_start_end_greater() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(102))
            .to_start_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_end_bound()),
        BoundOrdering::Greater,
    );
}

#[test]
fn rel_end_start_less() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_end_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(102)).to_start_bound()),
        BoundOrdering::Less,
    );
}

#[test]
fn rel_end_start_equal_inclusive_inclusive() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_end_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_start_bound()),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn rel_end_start_equal_inclusive_exclusive() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_end_bound()
            .bound_cmp(
                &RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(101),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn rel_end_start_equal_exclusive_inclusive() {
    assert_eq!(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(101), BoundInclusivity::Exclusive,)
            .to_end_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_start_bound()),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn rel_end_start_equal_exclusive_exclusive() {
    assert_eq!(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(101), BoundInclusivity::Exclusive,)
            .to_end_bound()
            .bound_cmp(
                &RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(101),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::StartEnd(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn rel_end_start_greater_inf_future_inf_past() {
    assert_eq!(
        RelEndBound::InfiniteFuture.bound_cmp(&RelStartBound::InfinitePast),
        BoundOrdering::Greater,
    );
}

#[test]
fn rel_end_start_greater_inf_future_finite() {
    assert_eq!(
        RelEndBound::InfiniteFuture
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_start_bound()),
        BoundOrdering::Greater,
    );
}

#[test]
fn rel_end_start_greater_finite_inf_past() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_end_bound()
            .bound_cmp(&RelStartBound::InfinitePast),
        BoundOrdering::Greater,
    );
}

#[test]
fn rel_end_start_greater_finite_finite() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(102))
            .to_end_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_start_bound()),
        BoundOrdering::Greater,
    );
}

#[test]
fn rel_end_end_less_finite_inf_future() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_end_bound()
            .bound_cmp(&RelEndBound::InfiniteFuture),
        BoundOrdering::Less,
    );
}

#[test]
fn rel_end_end_less_finite_finite() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_end_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(102)).to_end_bound()),
        BoundOrdering::Less,
    );
}

#[test]
fn rel_end_end_equal_inf_future_inf_future() {
    assert_eq!(
        RelEndBound::InfiniteFuture.bound_cmp(&RelEndBound::InfiniteFuture),
        BoundOrdering::Equal(None),
    );
}

#[test]
fn rel_end_end_equal_inclusive_inclusive() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_end_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_end_bound()),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn rel_end_end_equal_inclusive_exclusive() {
    assert_eq!(
        RelFiniteBoundPos::new(SignedDuration::from_hours(101))
            .to_end_bound()
            .bound_cmp(
                &RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(101),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Inclusive,
        ))),
    );
}

#[test]
fn rel_end_end_equal_exclusive_inclusive() {
    assert_eq!(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(101), BoundInclusivity::Exclusive,)
            .to_end_bound()
            .bound_cmp(&RelFiniteBoundPos::new(SignedDuration::from_hours(101)).to_end_bound()),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Inclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

#[test]
fn rel_end_end_equal_exclusive_exclusive() {
    assert_eq!(
        RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(101), BoundInclusivity::Exclusive,)
            .to_end_bound()
            .bound_cmp(
                &RelFiniteBoundPos::new_with_incl(
                    SignedDuration::from_hours(101),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound()
            ),
        BoundOrdering::Equal(Some(BoundOverlapAmbiguity::BothEnds(
            BoundInclusivity::Exclusive,
            BoundInclusivity::Exclusive,
        ))),
    );
}

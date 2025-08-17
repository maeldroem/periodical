use chrono::Utc;

use super::overlap::*;

use crate::intervals::absolute::{
    AbsoluteBounds, AbsoluteEndBound, AbsoluteStartBound, ClosedAbsoluteInterval, EmptiableAbsoluteBounds,
    HalfOpenAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;
use crate::test_utils::date;

#[test]
fn strip_overlap_position() {
    assert_eq!(OverlapPosition::OutsideBefore.strip(), DisambiguatedOverlapPosition::OutsideBefore);
    assert_eq!(OverlapPosition::OutsideAfter.strip(), DisambiguatedOverlapPosition::OutsideAfter);
    assert_eq!(OverlapPosition::Outside.strip(), DisambiguatedOverlapPosition::Outside);
    assert_eq!(
        OverlapPosition::EndsOnStart(
            BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
        ).strip(),
        DisambiguatedOverlapPosition::EndsOnStart,
    );
    assert_eq!(
        OverlapPosition::StartsOnEnd(
            BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
        ).strip(),
        DisambiguatedOverlapPosition::StartsOnEnd,
    );
    assert_eq!(OverlapPosition::CrossesStart.strip(), DisambiguatedOverlapPosition::CrossesStart);
    assert_eq!(OverlapPosition::CrossesEnd.strip(), DisambiguatedOverlapPosition::CrossesEnd);
    assert_eq!(OverlapPosition::Inside.strip(), DisambiguatedOverlapPosition::Inside);
    assert_eq!(
        OverlapPosition::InsideAndSameStart(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive))
        ).strip(),
        DisambiguatedOverlapPosition::InsideAndSameStart,
    );
    assert_eq!(
        OverlapPosition::InsideAndSameEnd(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive))
        ).strip(),
        DisambiguatedOverlapPosition::InsideAndSameEnd,
    );
    assert_eq!(
        OverlapPosition::Equal(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)),
            Some(BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)),
        ).strip(),
        DisambiguatedOverlapPosition::Equal,
    );
    assert_eq!(
        OverlapPosition::ContainsAndSameStart(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive))
        ).strip(),
        DisambiguatedOverlapPosition::ContainsAndSameStart,
    );
    assert_eq!(
        OverlapPosition::ContainsAndSameEnd(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive))
        ).strip(),
        DisambiguatedOverlapPosition::ContainsAndSameEnd,
    );
    assert_eq!(OverlapPosition::Contains.strip(), DisambiguatedOverlapPosition::Contains);
}

#[test]
fn overlap_position_empty_empty() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty.overlap_position(&EmptiableAbsoluteBounds::Empty),
        Ok(OverlapPosition::Outside),
    );
}

#[test]
fn overlap_position_empty_open() {
    assert_eq!(
        EmptiableAbsoluteBounds::Empty
            .overlap_position(&AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)),
        Ok(OverlapPosition::Outside),
    );
}

#[test]
fn overlap_position_open_empty() {
    assert_eq!(
        AbsoluteBounds::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
            .overlap_position(&EmptiableAbsoluteBounds::Empty),
        Ok(OverlapPosition::Outside),
    );
}

#[test]
fn overlap_position_half_open_equal() {
    assert_eq!(
        HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture)
            .overlap_position(&HalfOpenAbsoluteInterval::new(date(&Utc, 2025, 1, 1), OpeningDirection::ToFuture)),
        Ok(OverlapPosition::Equal(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)),
            None,
        )),
    );
}

#[test]
fn overlap_position_half_open_exclusive_inclusive() {
    assert_eq!(
        HalfOpenAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            OpeningDirection::ToFuture,
        )
            .overlap_position(&HalfOpenAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            )),
        Ok(OverlapPosition::Equal(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)),
            None,
        )),
    );
}

#[test]
fn overlap_position_closed_equal_various_bound_inclusivities() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .overlap_position(&ClosedAbsoluteInterval::new_with_inclusivity(
                date(&Utc, 2025, 1, 1),
                BoundInclusivity::Inclusive,
                date(&Utc, 2025, 1, 2),
                BoundInclusivity::Exclusive,
            )),
        Ok(OverlapPosition::Equal(
            Some(BoundOverlapAmbiguity::BothStarts(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)),
            Some(BoundOverlapAmbiguity::BothEnds(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)),
        )),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_time_gap_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2))
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new(
                    date(&Utc, 2025, 1, 3),
                    date(&Utc, 2025, 1, 4),
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideBefore),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_inclusive_inclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::EndsOnStart),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_inclusive_exclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideBefore),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_exclusive_inclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideBefore),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_exclusive_exclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideBefore),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_time_gap_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 3), date(&Utc, 2025, 1, 4))
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideAfter),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_inclusive_inclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::StartsOnEnd),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_inclusive_exclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideAfter),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_exclusive_inclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideAfter),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_exclusive_exclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideAfter),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_crosses_start() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 4),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesStart),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_crosses_end() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 4),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesEnd),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_inside() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 4),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::Inside),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_time_gap_inside_and_same_start() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_inside_and_same_start_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_inside_and_same_start_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesStart),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_inside_and_same_start_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::Inside),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_inside_and_same_start_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_time_gap_inside_and_same_end() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_inside_and_same_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_inside_and_same_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesEnd),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_inside_and_same_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::Inside),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_inside_and_same_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_inclusive_inclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_inclusive_inclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_inclusive_inclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_inclusive_inclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_inclusive_exclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_inclusive_exclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::Contains),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_inclusive_exclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesStart),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_inclusive_exclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_exclusive_inclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_exclusive_inclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesEnd),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_exclusive_inclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::Inside),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_exclusive_inclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_exclusive_exclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_exclusive_exclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_exclusive_exclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_equal_start_exclusive_exclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_contains_and_same_start_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_contains_and_same_start_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::Contains),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_contains_and_same_start_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesEnd),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_contains_and_same_start_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_contains_and_same_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_contains_and_same_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::Contains),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_contains_and_same_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesStart),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_contains_and_same_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_strict_closed_contains() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 4),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
        Ok(DisambiguatedOverlapPosition::Contains),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_time_gap_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2))
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new(
                    date(&Utc, 2025, 1, 3),
                    date(&Utc, 2025, 1, 4),
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideBefore),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_inclusive_inclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::EndsOnStart),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_inclusive_exclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::EndsOnStart),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_exclusive_inclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::EndsOnStart),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_exclusive_exclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideBefore),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_time_gap_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 3), date(&Utc, 2025, 1, 4))
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideAfter),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_inclusive_inclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::StartsOnEnd),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_inclusive_exclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::StartsOnEnd),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_exclusive_inclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::StartsOnEnd),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_exclusive_exclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideAfter),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_crosses_start() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 4),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesStart),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_crosses_end() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 4),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesEnd),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_inside() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 4),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Inside),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_time_gap_inside_and_same_start() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_inside_and_same_start_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_inside_and_same_start_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_inside_and_same_start_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_inside_and_same_start_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_time_gap_inside_and_same_end() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_inside_and_same_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_inside_and_same_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_inside_and_same_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_inside_and_same_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_inclusive_inclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_inclusive_inclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_inclusive_inclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_inclusive_inclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_inclusive_exclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_inclusive_exclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_inclusive_exclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_inclusive_exclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_exclusive_inclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_exclusive_inclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_exclusive_inclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_exclusive_inclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_exclusive_exclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_exclusive_exclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_exclusive_exclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_equal_start_exclusive_exclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_contains_and_same_start_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_contains_and_same_start_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_contains_and_same_start_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_contains_and_same_start_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_contains_and_same_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_contains_and_same_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_contains_and_same_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_contains_and_same_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_lenient_closed_contains() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 4),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
        Ok(DisambiguatedOverlapPosition::Contains),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_time_gap_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2))
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new(
                    date(&Utc, 2025, 1, 3),
                    date(&Utc, 2025, 1, 4),
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideBefore),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_inclusive_inclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::EndsOnStart),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_inclusive_exclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::EndsOnStart),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_exclusive_inclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::EndsOnStart),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_exclusive_exclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::EndsOnStart),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_time_gap_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 3), date(&Utc, 2025, 1, 4))
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideAfter),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_inclusive_inclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::StartsOnEnd),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_inclusive_exclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::StartsOnEnd),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_exclusive_inclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::StartsOnEnd),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_exclusive_exclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::StartsOnEnd),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_crosses_start() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 4),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesStart),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_crosses_end() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 4),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesEnd),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_inside() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 4),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Inside),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_time_gap_inside_and_same_start() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_inside_and_same_start_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_inside_and_same_start_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_inside_and_same_start_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_inside_and_same_start_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_time_gap_inside_and_same_end() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_inside_and_same_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_inside_and_same_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_inside_and_same_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_inside_and_same_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_inclusive_inclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_inclusive_inclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_inclusive_inclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_inclusive_inclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_inclusive_exclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_inclusive_exclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_inclusive_exclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_inclusive_exclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_exclusive_inclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_exclusive_inclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_exclusive_inclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_exclusive_inclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_exclusive_exclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_exclusive_exclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_exclusive_exclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_equal_start_exclusive_exclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_contains_and_same_start_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_contains_and_same_start_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_contains_and_same_start_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_contains_and_same_start_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_contains_and_same_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_contains_and_same_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_contains_and_same_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_contains_and_same_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_very_lenient_closed_contains() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 4),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
        Ok(DisambiguatedOverlapPosition::Contains),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_time_gap_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2))
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new(
                    date(&Utc, 2025, 1, 3),
                    date(&Utc, 2025, 1, 4),
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideBefore),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_inclusive_inclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::EndsOnStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_inclusive_exclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideBefore),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_exclusive_inclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::EndsOnStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_exclusive_exclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideBefore),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_time_gap_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 3), date(&Utc, 2025, 1, 4))
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideAfter),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_inclusive_inclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::StartsOnEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_inclusive_exclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::StartsOnEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_exclusive_inclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideAfter),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_exclusive_exclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideAfter),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_crosses_start() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 4),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_crosses_end() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 4),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_inside() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 4),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::Inside),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_time_gap_inside_and_same_start() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_inside_and_same_start_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_inside_and_same_start_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_inside_and_same_start_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::Inside),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_inside_and_same_start_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_time_gap_inside_and_same_end() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_inside_and_same_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_inside_and_same_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_inside_and_same_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::Inside),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_inside_and_same_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_inclusive_inclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_inclusive_inclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_inclusive_inclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_inclusive_inclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_inclusive_exclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_inclusive_exclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::Contains),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_inclusive_exclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_inclusive_exclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_exclusive_inclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_exclusive_inclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_exclusive_inclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::Inside),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_exclusive_inclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_exclusive_exclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_exclusive_exclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_exclusive_exclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_equal_start_exclusive_exclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_contains_and_same_start_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_contains_and_same_start_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::Contains),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_contains_and_same_start_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_contains_and_same_start_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_contains_and_same_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_contains_and_same_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::Contains),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_contains_and_same_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_contains_and_same_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_future_closed_contains() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 4),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
        Ok(DisambiguatedOverlapPosition::Contains),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_time_gap_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2))
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new(
                    date(&Utc, 2025, 1, 3),
                    date(&Utc, 2025, 1, 4),
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideBefore),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_inclusive_inclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::EndsOnStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_inclusive_exclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::EndsOnStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_exclusive_inclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideBefore),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_exclusive_exclusive_adjacency_before_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideBefore),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_time_gap_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 3), date(&Utc, 2025, 1, 4))
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new(date(&Utc, 2025, 1, 1), date(&Utc, 2025, 1, 2)),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideAfter),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_inclusive_inclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::StartsOnEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_inclusive_exclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideAfter),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_exclusive_inclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::StartsOnEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_exclusive_exclusive_adjacency_after_other() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::OutsideAfter),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_crosses_start() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 4),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_crosses_end() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 4),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_inside() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 4),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::Inside),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_time_gap_inside_and_same_start() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_inside_and_same_start_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_inside_and_same_start_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_inside_and_same_start_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::Inside),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_inside_and_same_start_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_time_gap_inside_and_same_end() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_inside_and_same_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_inside_and_same_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_inside_and_same_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::Inside),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_inside_and_same_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_inclusive_inclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_inclusive_inclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_inclusive_inclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_inclusive_inclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_inclusive_exclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_inclusive_exclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::Contains),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_inclusive_exclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_inclusive_exclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_exclusive_inclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_exclusive_inclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_exclusive_inclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::Inside),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_exclusive_inclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_exclusive_exclusive_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_exclusive_exclusive_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_exclusive_exclusive_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_equal_start_exclusive_exclusive_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 2),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::Equal),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_contains_and_same_start_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_contains_and_same_start_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::Contains),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_contains_and_same_start_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_contains_and_same_start_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Exclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 1),
                    BoundInclusivity::Exclusive,
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_contains_and_same_end_inclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_contains_and_same_end_inclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::Contains),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_contains_and_same_end_exclusive_inclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::CrossesStart),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_contains_and_same_end_exclusive_exclusive() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 3),
            BoundInclusivity::Exclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
    );
}

#[test]
fn disambiguated_overlap_position_continuous_to_past_closed_contains() {
    assert_eq!(
        ClosedAbsoluteInterval::new_with_inclusivity(
            date(&Utc, 2025, 1, 1),
            BoundInclusivity::Inclusive,
            date(&Utc, 2025, 1, 4),
            BoundInclusivity::Inclusive,
        )
            .disambiguated_overlap_position(
                &ClosedAbsoluteInterval::new_with_inclusivity(
                    date(&Utc, 2025, 1, 2),
                    BoundInclusivity::Inclusive,
                    date(&Utc, 2025, 1, 3),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
        Ok(DisambiguatedOverlapPosition::Contains),
    );
}

#[test]
fn overlap_rule_allow_adjacency_true_ends_on_start() {
    assert!(OverlapRule::AllowAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::EndsOnStart));
}

#[test]
fn overlap_rule_allow_adjacency_true_starts_on_end() {
    assert!(OverlapRule::AllowAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::StartsOnEnd));
}

#[test]
fn overlap_rule_allow_adjacency_true_outside() {
    assert!(OverlapRule::AllowAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::Outside));
}

#[test]
fn overlap_rule_allow_adjacency_false_ends_on_start() {
    assert!(OverlapRule::AllowAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::EndsOnStart));
}

#[test]
fn overlap_rule_allow_adjacency_false_starts_on_end() {
    assert!(OverlapRule::AllowAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::StartsOnEnd));
}

#[test]
fn overlap_rule_allow_adjacency_false_outside() {
    assert!(!OverlapRule::AllowAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::Outside));
}

#[test]
fn overlap_rule_allow_past_adjacency_true_ends_on_start() {
    assert!(OverlapRule::AllowPastAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::EndsOnStart));
}

#[test]
fn overlap_rule_allow_past_adjacency_true_starts_on_end() {
    assert!(OverlapRule::AllowPastAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::StartsOnEnd));
}

#[test]
fn overlap_rule_allow_past_adjacency_true_outside() {
    assert!(OverlapRule::AllowPastAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::Outside));
}

#[test]
fn overlap_rule_allow_past_adjacency_false_ends_on_start() {
    assert!(OverlapRule::AllowPastAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::EndsOnStart));
}

#[test]
fn overlap_rule_allow_past_adjacency_false_starts_on_end() {
    assert!(!OverlapRule::AllowPastAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::StartsOnEnd));
}

#[test]
fn overlap_rule_allow_past_adjacency_false_outside() {
    assert!(!OverlapRule::AllowPastAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::Outside));
}

#[test]
fn overlap_rule_allow_future_adjacency_true_ends_on_start() {
    assert!(OverlapRule::AllowFutureAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::EndsOnStart));
}

#[test]
fn overlap_rule_allow_future_adjacency_true_starts_on_end() {
    assert!(OverlapRule::AllowFutureAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::StartsOnEnd));
}

#[test]
fn overlap_rule_allow_future_adjacency_true_outside() {
    assert!(OverlapRule::AllowFutureAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::Outside));
}

#[test]
fn overlap_rule_allow_future_adjacency_false_ends_on_start() {
    assert!(!OverlapRule::AllowFutureAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::EndsOnStart));
}

#[test]
fn overlap_rule_allow_future_adjacency_false_starts_on_end() {
    assert!(OverlapRule::AllowFutureAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::StartsOnEnd));
}

#[test]
fn overlap_rule_allow_future_adjacency_false_outside() {
    assert!(!OverlapRule::AllowFutureAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::Outside));
}

#[test]
fn overlap_rule_deny_adjacency_true_ends_on_start() {
    assert!(!OverlapRule::DenyAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::EndsOnStart));
}

#[test]
fn overlap_rule_deny_adjacency_true_starts_on_end() {
    assert!(!OverlapRule::DenyAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::StartsOnEnd));
}

#[test]
fn overlap_rule_deny_adjacency_true_outside() {
    assert!(OverlapRule::DenyAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::Outside));
}

#[test]
fn overlap_rule_deny_adjacency_false_ends_on_start() {
    assert!(!OverlapRule::DenyAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::EndsOnStart));
}

#[test]
fn overlap_rule_deny_adjacency_false_starts_on_end() {
    assert!(!OverlapRule::DenyAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::StartsOnEnd));
}

#[test]
fn overlap_rule_deny_adjacency_false_outside() {
    assert!(!OverlapRule::DenyAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::Outside));
}

#[test]
fn overlap_rule_deny_past_adjacency_true_ends_on_start() {
    assert!(!OverlapRule::DenyPastAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::EndsOnStart));
}

#[test]
fn overlap_rule_deny_past_adjacency_true_starts_on_end() {
    assert!(OverlapRule::DenyPastAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::StartsOnEnd));
}

#[test]
fn overlap_rule_deny_past_adjacency_true_outside() {
    assert!(OverlapRule::DenyPastAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::Outside));
}

#[test]
fn overlap_rule_deny_past_adjacency_false_ends_on_start() {
    assert!(!OverlapRule::DenyPastAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::EndsOnStart));
}

#[test]
fn overlap_rule_deny_past_adjacency_false_starts_on_end() {
    assert!(!OverlapRule::DenyPastAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::StartsOnEnd));
}

#[test]
fn overlap_rule_deny_past_adjacency_false_outside() {
    assert!(!OverlapRule::DenyPastAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::Outside));
}

#[test]
fn overlap_rule_deny_future_adjacency_true_ends_on_start() {
    assert!(OverlapRule::DenyFutureAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::EndsOnStart));
}

#[test]
fn overlap_rule_deny_future_adjacency_true_starts_on_end() {
    assert!(!OverlapRule::DenyFutureAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::StartsOnEnd));
}

#[test]
fn overlap_rule_deny_future_adjacency_true_outside() {
    assert!(OverlapRule::DenyFutureAdjacency.counts_as_overlap(true, DisambiguatedOverlapPosition::Outside));
}

#[test]
fn overlap_rule_deny_future_adjacency_false_ends_on_start() {
    assert!(!OverlapRule::DenyFutureAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::EndsOnStart));
}

#[test]
fn overlap_rule_deny_future_adjacency_false_starts_on_end() {
    assert!(!OverlapRule::DenyFutureAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::StartsOnEnd));
}

#[test]
fn overlap_rule_deny_future_adjacency_false_outside() {
    assert!(!OverlapRule::DenyFutureAdjacency.counts_as_overlap(false, DisambiguatedOverlapPosition::Outside));
}

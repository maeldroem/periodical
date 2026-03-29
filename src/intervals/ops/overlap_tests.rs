use std::error::Error;

use jiff::Zoned;

use super::overlap::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    HalfBoundedAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::ops::bound_overlap_ambiguity::BoundOverlapAmbiguity;

mod overlap_position {
    use super::*;

    #[test]
    fn strip() {
        assert_eq!(
            OverlapPosition::OutsideBefore.strip(),
            DisambiguatedOverlapPosition::OutsideBefore
        );
        assert_eq!(
            OverlapPosition::OutsideAfter.strip(),
            DisambiguatedOverlapPosition::OutsideAfter
        );
        assert_eq!(OverlapPosition::Outside.strip(), DisambiguatedOverlapPosition::Outside);
        assert_eq!(
            OverlapPosition::EndsOnStart(BoundOverlapAmbiguity::BothStarts(
                BoundInclusivity::Inclusive,
                BoundInclusivity::Inclusive
            ))
            .strip(),
            DisambiguatedOverlapPosition::EndsOnStart,
        );
        assert_eq!(
            OverlapPosition::StartsOnEnd(BoundOverlapAmbiguity::BothStarts(
                BoundInclusivity::Inclusive,
                BoundInclusivity::Inclusive
            ))
            .strip(),
            DisambiguatedOverlapPosition::StartsOnEnd,
        );
        assert_eq!(
            OverlapPosition::CrossesStart.strip(),
            DisambiguatedOverlapPosition::CrossesStart
        );
        assert_eq!(
            OverlapPosition::CrossesEnd.strip(),
            DisambiguatedOverlapPosition::CrossesEnd
        );
        assert_eq!(OverlapPosition::Inside.strip(), DisambiguatedOverlapPosition::Inside);
        assert_eq!(
            OverlapPosition::InsideAndSameStart(Some(BoundOverlapAmbiguity::BothStarts(
                BoundInclusivity::Inclusive,
                BoundInclusivity::Inclusive
            )))
            .strip(),
            DisambiguatedOverlapPosition::InsideAndSameStart,
        );
        assert_eq!(
            OverlapPosition::InsideAndSameEnd(Some(BoundOverlapAmbiguity::BothStarts(
                BoundInclusivity::Inclusive,
                BoundInclusivity::Inclusive
            )))
            .strip(),
            DisambiguatedOverlapPosition::InsideAndSameEnd,
        );
        assert_eq!(
            OverlapPosition::Equal(
                Some(BoundOverlapAmbiguity::BothStarts(
                    BoundInclusivity::Inclusive,
                    BoundInclusivity::Inclusive
                )),
                Some(BoundOverlapAmbiguity::BothEnds(
                    BoundInclusivity::Inclusive,
                    BoundInclusivity::Inclusive
                )),
            )
            .strip(),
            DisambiguatedOverlapPosition::Equal,
        );
        assert_eq!(
            OverlapPosition::ContainsAndSameStart(Some(BoundOverlapAmbiguity::BothStarts(
                BoundInclusivity::Inclusive,
                BoundInclusivity::Inclusive
            )))
            .strip(),
            DisambiguatedOverlapPosition::ContainsAndSameStart,
        );
        assert_eq!(
            OverlapPosition::ContainsAndSameEnd(Some(BoundOverlapAmbiguity::BothStarts(
                BoundInclusivity::Inclusive,
                BoundInclusivity::Inclusive
            )))
            .strip(),
            DisambiguatedOverlapPosition::ContainsAndSameEnd,
        );
        assert_eq!(
            OverlapPosition::Contains.strip(),
            DisambiguatedOverlapPosition::Contains
        );
    }

    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableAbsoluteBoundPair::Empty.overlap_position(&EmptiableAbsoluteBoundPair::Empty),
            Ok(OverlapPosition::Outside),
        );
    }

    #[test]
    fn empty_unbounded() {
        assert_eq!(
            EmptiableAbsoluteBoundPair::Empty.overlap_position(&AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture
            )),
            Ok(OverlapPosition::Outside),
        );
    }

    #[test]
    fn unbounded_empty() {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
                .overlap_position(&EmptiableAbsoluteBoundPair::Empty),
            Ok(OverlapPosition::Outside),
        );
    }

    #[test]
    fn half_bounded_equal() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            HalfBoundedAbsoluteInterval::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                OpeningDirection::ToFuture
            )
            .overlap_position(&HalfBoundedAbsoluteInterval::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                OpeningDirection::ToFuture
            )),
            Ok(OverlapPosition::Equal(
                Some(BoundOverlapAmbiguity::BothStarts(
                    BoundInclusivity::Inclusive,
                    BoundInclusivity::Inclusive
                )),
                None,
            )),
        );

        Ok(())
    }

    #[test]
    fn half_bounded_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            HalfBoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture,
            )
            .overlap_position(&HalfBoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                OpeningDirection::ToFuture,
            )),
            Ok(OverlapPosition::Equal(
                Some(BoundOverlapAmbiguity::BothStarts(
                    BoundInclusivity::Exclusive,
                    BoundInclusivity::Inclusive
                )),
                None,
            )),
        );

        Ok(())
    }

    #[test]
    fn bounded_equal_various_bound_inclusivities() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .overlap_position(&BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )),
            Ok(OverlapPosition::Equal(
                Some(BoundOverlapAmbiguity::BothStarts(
                    BoundInclusivity::Exclusive,
                    BoundInclusivity::Inclusive
                )),
                Some(BoundOverlapAmbiguity::BothEnds(
                    BoundInclusivity::Inclusive,
                    BoundInclusivity::Exclusive
                )),
            )),
        );

        Ok(())
    }
}

mod disambiguated_overlap_position {
    use super::*;

    #[test]
    fn strict_bounded_time_gap_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideBefore),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_inclusive_inclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::EndsOnStart),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_inclusive_exclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideBefore),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_exclusive_inclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideBefore),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_exclusive_exclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideBefore),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_time_gap_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideAfter),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_inclusive_inclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::StartsOnEnd),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_inclusive_exclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideAfter),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_exclusive_inclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideAfter),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_exclusive_exclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideAfter),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_crosses_start() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesStart),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_crosses_end() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesEnd),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_inside() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::Inside),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_time_gap_inside_and_same_start() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_inside_and_same_start_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_inside_and_same_start_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesStart),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_inside_and_same_start_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::Inside),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_inside_and_same_start_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_time_gap_inside_and_same_end() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_inside_and_same_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_inside_and_same_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesEnd),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_inside_and_same_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::Inside),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_inside_and_same_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_inclusive_inclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_inclusive_inclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_inclusive_inclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_inclusive_inclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_inclusive_exclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_inclusive_exclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::Contains),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_inclusive_exclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesStart),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_inclusive_exclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_exclusive_inclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_exclusive_inclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesEnd),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_exclusive_inclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::Inside),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_exclusive_inclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_exclusive_exclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_exclusive_exclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_exclusive_exclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_equal_start_exclusive_exclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_contains_and_same_start_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_contains_and_same_start_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::Contains),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_contains_and_same_start_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesEnd),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_contains_and_same_start_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_contains_and_same_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_contains_and_same_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::Contains),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_contains_and_same_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesStart),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_contains_and_same_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn strict_bounded_contains() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Strict,
            ),
            Ok(DisambiguatedOverlapPosition::Contains),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_time_gap_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideBefore),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_inclusive_inclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::EndsOnStart),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_inclusive_exclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::EndsOnStart),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_exclusive_inclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::EndsOnStart),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_exclusive_exclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideBefore),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_time_gap_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideAfter),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_inclusive_inclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::StartsOnEnd),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_inclusive_exclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::StartsOnEnd),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_exclusive_inclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::StartsOnEnd),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_exclusive_exclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideAfter),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_crosses_start() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesStart),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_crosses_end() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesEnd),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_inside() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Inside),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_time_gap_inside_and_same_start() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_inside_and_same_start_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_inside_and_same_start_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_inside_and_same_start_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_inside_and_same_start_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_time_gap_inside_and_same_end() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_inside_and_same_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_inside_and_same_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_inside_and_same_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_inside_and_same_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_inclusive_inclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_inclusive_inclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_inclusive_inclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_inclusive_inclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_inclusive_exclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_inclusive_exclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_inclusive_exclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_inclusive_exclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_exclusive_inclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_exclusive_inclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_exclusive_inclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_exclusive_inclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_exclusive_exclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_exclusive_exclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_exclusive_exclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_equal_start_exclusive_exclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_contains_and_same_start_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_contains_and_same_start_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_contains_and_same_start_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_contains_and_same_start_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_contains_and_same_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_contains_and_same_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_contains_and_same_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_contains_and_same_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn lenient_bounded_contains() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::Lenient,
            ),
            Ok(DisambiguatedOverlapPosition::Contains),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_time_gap_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideBefore),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_inclusive_inclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::EndsOnStart),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_inclusive_exclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::EndsOnStart),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_exclusive_inclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::EndsOnStart),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_exclusive_exclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::EndsOnStart),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_time_gap_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideAfter),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_inclusive_inclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::StartsOnEnd),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_inclusive_exclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::StartsOnEnd),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_exclusive_inclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::StartsOnEnd),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_exclusive_exclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::StartsOnEnd),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_crosses_start() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesStart),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_crosses_end() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesEnd),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_inside() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Inside),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_time_gap_inside_and_same_start() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_inside_and_same_start_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_inside_and_same_start_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_inside_and_same_start_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_inside_and_same_start_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_time_gap_inside_and_same_end() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_inside_and_same_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_inside_and_same_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_inside_and_same_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_inside_and_same_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_inclusive_inclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_inclusive_inclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_inclusive_inclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_inclusive_inclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_inclusive_exclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_inclusive_exclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_inclusive_exclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_inclusive_exclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_exclusive_inclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_exclusive_inclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_exclusive_inclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_exclusive_inclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_exclusive_exclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_exclusive_exclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_exclusive_exclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_equal_start_exclusive_exclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_contains_and_same_start_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_contains_and_same_start_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_contains_and_same_start_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_contains_and_same_start_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_contains_and_same_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_contains_and_same_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_contains_and_same_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_contains_and_same_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn very_lenient_bounded_contains() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::VeryLenient,
            ),
            Ok(DisambiguatedOverlapPosition::Contains),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_time_gap_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideBefore),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_inclusive_inclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::EndsOnStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_inclusive_exclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideBefore),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_exclusive_inclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::EndsOnStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_exclusive_exclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideBefore),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_time_gap_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideAfter),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_inclusive_inclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::StartsOnEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_inclusive_exclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::StartsOnEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_exclusive_inclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideAfter),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_exclusive_exclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideAfter),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_crosses_start() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_crosses_end() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_inside() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::Inside),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_time_gap_inside_and_same_start() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_inside_and_same_start_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_inside_and_same_start_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_inside_and_same_start_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::Inside),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_inside_and_same_start_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_time_gap_inside_and_same_end() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_inside_and_same_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_inside_and_same_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_inside_and_same_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::Inside),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_inside_and_same_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_inclusive_inclusive_end_inclusive_inclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_inclusive_inclusive_end_inclusive_exclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_inclusive_inclusive_end_exclusive_inclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_inclusive_inclusive_end_exclusive_exclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_inclusive_exclusive_end_inclusive_inclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_inclusive_exclusive_end_inclusive_exclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::Contains),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_inclusive_exclusive_end_exclusive_inclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_inclusive_exclusive_end_exclusive_exclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_exclusive_inclusive_end_inclusive_inclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_exclusive_inclusive_end_inclusive_exclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_exclusive_inclusive_end_exclusive_inclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::Inside),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_exclusive_inclusive_end_exclusive_exclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_exclusive_exclusive_end_inclusive_inclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_exclusive_exclusive_end_inclusive_exclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_exclusive_exclusive_end_exclusive_inclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_equal_start_exclusive_exclusive_end_exclusive_exclusive()
    -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_contains_and_same_start_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_contains_and_same_start_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::Contains),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_contains_and_same_start_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_contains_and_same_start_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_contains_and_same_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_contains_and_same_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::Contains),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_contains_and_same_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_contains_and_same_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_future_bounded_contains() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToFuture,
            ),
            Ok(DisambiguatedOverlapPosition::Contains),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_time_gap_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideBefore),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_inclusive_inclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::EndsOnStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_inclusive_exclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::EndsOnStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_exclusive_inclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideBefore),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_exclusive_exclusive_adjacency_before_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideBefore),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_time_gap_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new(
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideAfter),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_inclusive_inclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::StartsOnEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_inclusive_exclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideAfter),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_exclusive_inclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::StartsOnEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_exclusive_exclusive_adjacency_after_other() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::OutsideAfter),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_crosses_start() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_crosses_end() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_inside() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::Inside),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_time_gap_inside_and_same_start() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_inside_and_same_start_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_inside_and_same_start_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_inside_and_same_start_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::Inside),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_inside_and_same_start_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_time_gap_inside_and_same_end() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_inside_and_same_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_inside_and_same_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_inside_and_same_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::Inside),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_inside_and_same_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_inclusive_inclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_inclusive_inclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_inclusive_inclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_inclusive_inclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_inclusive_exclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_inclusive_exclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::Contains),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_inclusive_exclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_inclusive_exclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_exclusive_inclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_exclusive_inclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_exclusive_inclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::Inside),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_exclusive_inclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_exclusive_exclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_exclusive_exclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_exclusive_exclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::InsideAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_equal_start_exclusive_exclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::Equal),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_contains_and_same_start_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_contains_and_same_start_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::Contains),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_contains_and_same_start_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_contains_and_same_start_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_contains_and_same_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_contains_and_same_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::Contains),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_contains_and_same_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::CrossesStart),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_contains_and_same_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::ContainsAndSameEnd),
        );

        Ok(())
    }

    #[test]
    fn continuous_to_past_bounded_contains() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .disambiguated_overlap_position(
                &BoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                OverlapRuleSet::ContinuousToPast,
            ),
            Ok(DisambiguatedOverlapPosition::Contains),
        );

        Ok(())
    }
}

mod overlap_rule {
    use super::*;

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
}

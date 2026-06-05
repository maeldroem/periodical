use std::error::Error;

use jiff::Zoned;

use super::remove_overlap_or_gap::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsInterval,
    AbsStartBound,
    EmptiableAbsBoundPair,
    HalfBoundedAbsInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::UnboundedInterval;

mod overlap_or_gap_removal_result {
    use super::*;

    #[test]
    fn is_single() {
        assert!(OverlapOrGapRemovalResult::Single(()).is_single());
        assert!(!OverlapOrGapRemovalResult::Split((), ()).is_single());
    }

    #[test]
    fn is_split() {
        assert!(!OverlapOrGapRemovalResult::Single(()).is_split());
        assert!(OverlapOrGapRemovalResult::Split((), ()).is_split());
    }

    #[test]
    fn single_opt() {
        assert_eq!(OverlapOrGapRemovalResult::Single(10).single(), Some(10));
        assert_eq!(OverlapOrGapRemovalResult::Split(10, 20).single(), None);
    }

    #[test]
    fn split_opt() {
        assert_eq!(OverlapOrGapRemovalResult::Single(10).split(), None);
        assert_eq!(OverlapOrGapRemovalResult::Split(10, 20).split(), Some((10, 20)));
    }

    #[test]
    fn map() {
        assert_eq!(
            OverlapOrGapRemovalResult::Single(10).map(|x| x + 10),
            OverlapOrGapRemovalResult::Single(20)
        );
        assert_eq!(
            OverlapOrGapRemovalResult::Split(10, 20).map(|x| x + 10),
            OverlapOrGapRemovalResult::Split(20, 30)
        );
    }
}

mod remove_overlap_or_gap {
    use super::*;

    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableAbsBoundPair::Empty.remove_overlap_or_gap(&EmptiableAbsBoundPair::Empty),
            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Empty),
        );
    }

    #[test]
    fn empty_unbounded() {
        assert_eq!(
            EmptiableAbsBoundPair::Empty.remove_overlap_or_gap(&AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsEndBound::InfiniteFuture,
            )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Empty),
        );
    }

    #[test]
    fn unbounded_empty() {
        assert_eq!(
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture)
                .remove_overlap_or_gap(&EmptiableAbsBoundPair::Empty),
            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsEndBound::InfiniteFuture
            ))),
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture).remove_overlap_or_gap(
                &AbsBoundPair::new(AbsStartBound::InfinitePast, AbsEndBound::InfiniteFuture,)
            ),
            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Empty),
        );
    }

    #[test]
    fn gap_between_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
            )
            .remove_overlap_or_gap(&AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
            )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ))),
        );

        Ok(())
    }

    #[test]
    fn overlap_between_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
            )
            .remove_overlap_or_gap(&AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()).to_end_bound(),
            )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ))),
        );

        Ok(())
    }

    #[test]
    fn bounded_adjacent_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )
            .remove_overlap_or_gap(&AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ))),
        );

        Ok(())
    }

    #[test]
    fn bounded_adjacent_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )
            .remove_overlap_or_gap(&AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            ))),
        );

        Ok(())
    }

    #[test]
    fn bounded_adjacent_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            )
            .remove_overlap_or_gap(&AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            ))),
        );

        Ok(())
    }

    #[test]
    fn bounded_adjacent_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            )
            .remove_overlap_or_gap(&AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Bound(AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            ))),
        );

        Ok(())
    }

    #[test]
    fn bounded_on_unbounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )
            .remove_overlap_or_gap(&UnboundedInterval),
            OverlapOrGapRemovalResult::Single(EmptiableAbsBoundPair::Empty),
        );

        Ok(())
    }

    #[test]
    fn unbounded_on_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            UnboundedInterval.remove_overlap_or_gap(&AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )),
            OverlapOrGapRemovalResult::Split(
                AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time_incl(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToPast,
                ))
                .to_emptiable(),
                AbsInterval::HalfBounded(HalfBoundedAbsInterval::from_time_incl(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                ))
                .to_emptiable(),
            ),
        );

        Ok(())
    }
}

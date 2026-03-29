use std::error::Error;

use jiff::Zoned;

use super::remove_overlap_or_gap::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteInterval,
    AbsoluteStartBound,
    EmptiableAbsoluteBoundPair,
    HalfBoundedAbsoluteInterval,
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
            EmptiableAbsoluteBoundPair::Empty.remove_overlap_or_gap(&EmptiableAbsoluteBoundPair::Empty),
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty),
        );
    }

    #[test]
    fn empty_unbounded() {
        assert_eq!(
            EmptiableAbsoluteBoundPair::Empty.remove_overlap_or_gap(&AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty),
        );
    }

    #[test]
    fn unbounded_empty() {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
                .remove_overlap_or_gap(&EmptiableAbsoluteBoundPair::Empty),
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture
            ))),
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture)
                .remove_overlap_or_gap(&AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteEndBound::InfiniteFuture,
                )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty),
        );
    }

    #[test]
    fn gap_between_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
            )
            .remove_overlap_or_gap(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
            )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ))),
        );

        Ok(())
    }

    #[test]
    fn overlap_between_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
            )
            .remove_overlap_or_gap(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
            )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ))),
        );

        Ok(())
    }

    #[test]
    fn bounded_adjacent_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )
            .remove_overlap_or_gap(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ))),
        );

        Ok(())
    }

    #[test]
    fn bounded_adjacent_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )
            .remove_overlap_or_gap(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            ))),
        );

        Ok(())
    }

    #[test]
    fn bounded_adjacent_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            )
            .remove_overlap_or_gap(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ))),
        );

        Ok(())
    }

    #[test]
    fn bounded_adjacent_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            )
            .remove_overlap_or_gap(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            ))),
        );

        Ok(())
    }

    #[test]
    fn bounded_on_unbounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )
            .remove_overlap_or_gap(&UnboundedInterval),
            OverlapOrGapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty),
        );

        Ok(())
    }

    #[test]
    fn unbounded_on_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            UnboundedInterval.remove_overlap_or_gap(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            OverlapOrGapRemovalResult::Split(
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToPast,
                )).to_emptiable(),
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                )).to_emptiable(),
            ),
        );

        Ok(())
    }
}

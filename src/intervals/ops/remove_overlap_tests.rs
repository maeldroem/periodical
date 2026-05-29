use std::error::Error;

use jiff::Zoned;

use super::remove_overlap::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteStartBound,
    EmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::BoundInclusivity;

mod overlap_removal_result {
    use super::*;

    #[test]
    fn is_single() {
        assert!(OverlapRemovalResult::Single(()).is_single());
        assert!(!OverlapRemovalResult::Split((), ()).is_single());
    }

    #[test]
    fn is_split() {
        assert!(!OverlapRemovalResult::Single(()).is_split());
        assert!(OverlapRemovalResult::Split((), ()).is_split());
    }

    #[test]
    fn single_opt() {
        assert_eq!(OverlapRemovalResult::Single(10).single(), Some(10));
        assert_eq!(OverlapRemovalResult::Split(10, 20).single(), None);
    }

    #[test]
    fn split_opt() {
        assert_eq!(OverlapRemovalResult::Single(10).split(), None);
        assert_eq!(OverlapRemovalResult::Split(10, 20).split(), Some((10, 20)));
    }

    #[test]
    fn map() {
        assert_eq!(
            OverlapRemovalResult::Single(10).map(|x| x + 10),
            OverlapRemovalResult::Single(20)
        );
        assert_eq!(
            OverlapRemovalResult::Split(10, 20).map(|x| x + 10),
            OverlapRemovalResult::Split(20, 30)
        );
    }
}

mod remove_overlap {
    use super::*;

    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableAbsoluteBoundPair::Empty.remove_overlap(&EmptiableAbsoluteBoundPair::Empty),
            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty)),
        );
    }

    #[test]
    fn empty_unbounded() {
        assert_eq!(
            EmptiableAbsoluteBoundPair::Empty.remove_overlap(&AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty)),
        );
    }

    #[test]
    fn unbounded_empty() {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
                .remove_overlap(&EmptiableAbsoluteBoundPair::Empty),
            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Bound(
                AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
            ))),
        );
    }

    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,).remove_overlap(
                &AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
            ),
            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty)),
        );
    }

    #[test]
    fn bounded_no_overlap() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            )
            .remove_overlap(&AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            )),
            Err(OverlapRemovalNoOverlapFoundError),
        );

        Ok(())
    }

    #[test]
    fn bounded_adjacent_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )
            .remove_overlap(&AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )),
            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Bound(
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Inclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )
            ))),
        );

        Ok(())
    }

    #[test]
    fn bounded_adjacent_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )
            .remove_overlap(&AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )),
            Err(OverlapRemovalNoOverlapFoundError),
        );

        Ok(())
    }

    #[test]
    fn bounded_adjacent_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            )
            .remove_overlap(&AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )),
            Err(OverlapRemovalNoOverlapFoundError),
        );

        Ok(())
    }

    #[test]
    fn bounded_adjacent_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            )
            .remove_overlap(&AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )),
            Err(OverlapRemovalNoOverlapFoundError),
        );

        Ok(())
    }

    #[test]
    fn bounded_overlap() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )
            .remove_overlap(&AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )),
            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Bound(
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Inclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )
            ))),
        );

        Ok(())
    }

    #[test]
    fn bounded_on_unbounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )
                .to_end_bound(),
            )
            .remove_overlap(&AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
            Ok(OverlapRemovalResult::Single(EmptiableAbsoluteBoundPair::Empty)),
        );

        Ok(())
    }

    #[test]
    fn unbounded_on_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,).remove_overlap(
                &AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Inclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Inclusive,
                    )
                    .to_end_bound(),
                )
            ),
            Ok(OverlapRemovalResult::Split(
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                )),
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                )),
            )),
        );

        Ok(())
    }
}

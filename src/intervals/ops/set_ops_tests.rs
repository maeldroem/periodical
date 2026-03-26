use std::error::Error;

use jiff::Zoned;

use crate::intervals::absolute::{
    AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound, EmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::BoundInclusivity;
use crate::ops::{DifferenceResult, IntersectionResult, SymmetricDifferenceResult, UnionResult};

use super::set_ops::*;

mod unite {
    use super::*;
    
    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableAbsoluteBoundPair::Empty.unite(&EmptiableAbsoluteBoundPair::Empty),
            UnionResult::Separate,
        );
    }
    
    #[test]
    fn empty_unbounded() {
        assert_eq!(
            EmptiableAbsoluteBoundPair::Empty.unite(&AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
            UnionResult::Separate,
        );
    }
    
    #[test]
    fn unbounded_empty() {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
                .unite(&EmptiableAbsoluteBoundPair::Empty),
            UnionResult::Separate,
        );
    }
    
    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,).unite(
                &AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
            ),
            UnionResult::United(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
        );
    }
    
    #[test]
    fn bounded_no_overlap() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )
            .unite(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )),
            UnionResult::Separate,
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
            .unite(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            UnionResult::United(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
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
            .unite(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            UnionResult::United(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
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
            .unite(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            UnionResult::United(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
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
            .unite(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            UnionResult::Separate,
        );

        Ok(())
    }
    
    #[test]
    fn bounded_clear_overlap() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )
            .unite(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )),
            UnionResult::United(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )),
        );

        Ok(())
    }
    
    #[test]
    fn bounded_on_unbounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )
            .unite(&AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
            UnionResult::United(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
        );

        Ok(())
    }
    
    #[test]
    fn unbounded_on_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,).unite(
                &AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                )
            ),
            UnionResult::United(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
        );

        Ok(())
    }
}

mod intersect {
    use super::*;
    
    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableAbsoluteBoundPair::Empty.intersect(&EmptiableAbsoluteBoundPair::Empty),
            IntersectionResult::Separate,
        );
    }
    
    #[test]
    fn empty_unbounded() {
        assert_eq!(
            EmptiableAbsoluteBoundPair::Empty.intersect(&AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
            IntersectionResult::Separate,
        );
    }
    
    #[test]
    fn unbounded_empty() {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
                .intersect(&EmptiableAbsoluteBoundPair::Empty),
            IntersectionResult::Separate,
        );
    }
    
    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,).intersect(
                &AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
            ),
            IntersectionResult::Intersected(AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
        );
    }
    
    #[test]
    fn bounded_no_overlap() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )
            .intersect(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )),
            IntersectionResult::Separate,
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
            .intersect(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            IntersectionResult::Intersected(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
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
            .intersect(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            IntersectionResult::Separate,
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
            .intersect(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            IntersectionResult::Separate,
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
            .intersect(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            IntersectionResult::Separate,
        );

        Ok(())
    }
    
    #[test]
    fn bounded_clear_overlap() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )
            .intersect(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )),
            IntersectionResult::Intersected(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )),
        );

        Ok(())
    }
    
    #[test]
    fn bounded_on_unbounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )
            .intersect(&AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
            IntersectionResult::Intersected(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )),
        );

        Ok(())
    }
    
    #[test]
    fn unbounded_on_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,).intersect(
                &AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                )
            ),
            IntersectionResult::Intersected(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )),
        );

        Ok(())
    }
}

mod difference {
    use super::*;
    
    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableAbsoluteBoundPair::Empty.differentiate(&EmptiableAbsoluteBoundPair::Empty),
            DifferenceResult::Separate,
        );
    }
    
    #[test]
    fn empty_unbounded() {
        assert_eq!(
            EmptiableAbsoluteBoundPair::Empty.differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
            DifferenceResult::Separate,
        );
    }
    
    #[test]
    fn unbounded_empty() {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
                .differentiate(&EmptiableAbsoluteBoundPair::Empty),
            DifferenceResult::Separate,
        );
    }
    
    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,).differentiate(
                &AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
            ),
            DifferenceResult::Single(EmptiableAbsoluteBoundPair::Empty),
        );
    }
    
    #[test]
    fn bounded_no_overlap() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )
            .differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )),
            DifferenceResult::Separate,
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
            .differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            DifferenceResult::Single(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
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
            .differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            DifferenceResult::Separate,
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
            .differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            DifferenceResult::Separate,
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
            .differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            DifferenceResult::Separate,
        );

        Ok(())
    }
    
    #[test]
    fn bounded_clear_overlap() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )
            .differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )),
            DifferenceResult::Single(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
            ))),
        );

        Ok(())
    }
    
    #[test]
    fn bounded_on_unbounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )
            .differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
            DifferenceResult::Single(EmptiableAbsoluteBoundPair::Empty),
        );

        Ok(())
    }
    
    #[test]
    fn unbounded_on_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,).differentiate(
                &AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                )
            ),
            DifferenceResult::Split(
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                    AbsoluteEndBound::InfiniteFuture,
                )),
            ),
        );

        Ok(())
    }
}

mod sym_difference {
    use super::*;
    
    #[test]
    fn empty_empty() {
        assert_eq!(
            EmptiableAbsoluteBoundPair::Empty.symmetrically_differentiate(&EmptiableAbsoluteBoundPair::Empty),
            SymmetricDifferenceResult::Separate,
        );
    }
    
    #[test]
    fn empty_unbounded() {
        assert_eq!(
            EmptiableAbsoluteBoundPair::Empty.symmetrically_differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
            SymmetricDifferenceResult::Separate,
        );
    }
    
    #[test]
    fn unbounded_empty() {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
                .symmetrically_differentiate(&EmptiableAbsoluteBoundPair::Empty),
            SymmetricDifferenceResult::Separate,
        );
    }
    
    #[test]
    fn unbounded_unbounded() {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
                .symmetrically_differentiate(&AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteEndBound::InfiniteFuture,
                )),
            SymmetricDifferenceResult::Single(EmptiableAbsoluteBoundPair::Empty),
        );
    }
    
    #[test]
    fn bounded_no_overlap() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )
            .symmetrically_differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )),
            SymmetricDifferenceResult::Separate,
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
            .symmetrically_differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            SymmetricDifferenceResult::Split(
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Inclusive,
                    )),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Inclusive,
                    )),
                )),
            ),
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
            .symmetrically_differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            SymmetricDifferenceResult::Separate,
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
            .symmetrically_differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            SymmetricDifferenceResult::Separate,
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
            .symmetrically_differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
            )),
            SymmetricDifferenceResult::Separate,
        );

        Ok(())
    }
    
    #[test]
    fn bounded_clear_overlap() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )
            .symmetrically_differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )),
            SymmetricDifferenceResult::Split(
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Inclusive,
                    )),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Inclusive,
                    )),
                )),
            ),
        );

        Ok(())
    }
    
    #[test]
    fn bounded_on_unbounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
            )
            .symmetrically_differentiate(&AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::InfiniteFuture,
            )),
            SymmetricDifferenceResult::Split(
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                    AbsoluteEndBound::InfiniteFuture,
                )),
            ),
        );

        Ok(())
    }
    
    #[test]
    fn unbounded_on_bounded() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture,)
                .symmetrically_differentiate(&AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())),
                )),
            SymmetricDifferenceResult::Split(
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteEndBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                )),
                EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
                    AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                        "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                        BoundInclusivity::Exclusive,
                    )),
                    AbsoluteEndBound::InfiniteFuture,
                )),
            ),
        );

        Ok(())
    }
}

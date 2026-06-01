use super::cut::*;
use crate::intervals::absolute::{
    AbsoluteInterval,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    HalfBoundedAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

mod cut_type {
    use super::*;

    #[test]
    fn cut_type_past_bound_inclusivity() {
        assert_eq!(
            CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive).past_bound_inclusivity(),
            BoundInclusivity::Inclusive,
        );
        assert_eq!(
            CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive).past_bound_inclusivity(),
            BoundInclusivity::Exclusive,
        );
    }

    #[test]
    fn cut_type_future_bound_inclusivity() {
        assert_eq!(
            CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive).future_bound_inclusivity(),
            BoundInclusivity::Exclusive,
        );
        assert_eq!(
            CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive).future_bound_inclusivity(),
            BoundInclusivity::Inclusive,
        );
    }

    #[test]
    fn cut_type_opposite() {
        assert_eq!(
            CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive).opposite(),
            CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive),
        );
    }

    #[test]
    fn cut_type_from_bound_inclusivity_pair() {
        assert_eq!(
            CutType::from((BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)),
            CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive),
        );
    }
}

mod cut_result {
    use super::*;

    #[test]
    fn cut_result_is_uncut() {
        assert!(CutResult::<()>::Uncut.is_uncut());
        assert!(!CutResult::Cut((), ()).is_uncut());
    }

    #[test]
    fn cut_result_is_cut() {
        assert!(!CutResult::<()>::Uncut.is_cut());
        assert!(CutResult::Cut((), ()).is_cut());
    }

    #[test]
    fn cut_result_cut_opt() {
        assert_eq!(CutResult::<u8>::Uncut.cut(), None);
        assert_eq!(CutResult::<u8>::Cut(10, 20).cut(), Some((10, 20)));
    }

    #[test]
    fn cut_result_map_cut() {
        assert_eq!(
            CutResult::<u8>::Cut(10, 20).map_cut(|a, b| (a + 10, b + 20)),
            CutResult::Cut(20, 40)
        );
    }
}

mod cut_at {
    use std::error::Error;

    use jiff::{Timestamp, Zoned};

    use super::*;

    #[test]
    fn cut_at_empty_interval() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            <EmptyInterval as Cuttable<Timestamp>>::cut_at(
                &EmptyInterval,
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            ),
            CutResult::Uncut,
        );

        Ok(())
    }

    #[test]
    fn cut_at_emptiable_abs_bounds_empty() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            EmptiableAbsoluteBoundPair::Empty.cut_at(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            ),
            CutResult::Uncut,
        );

        Ok(())
    }

    #[test]
    fn cut_at_unbounded_interval_inclusive_inclusive_cut() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            UnboundedInterval.cut_at(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            ),
            CutResult::Cut(
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToPast,
                )),
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToFuture,
                )),
            ),
        );

        Ok(())
    }

    #[test]
    fn cut_at_unbounded_interval_inclusive_exclusive_cut() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            UnboundedInterval.cut_at(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            ),
            CutResult::Cut(
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToPast,
                )),
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                )),
            ),
        );

        Ok(())
    }

    #[test]
    fn cut_at_unbounded_interval_exclusive_inclusive_cut() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            UnboundedInterval.cut_at(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive)
            ),
            CutResult::Cut(
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                )),
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    OpeningDirection::ToFuture,
                )),
            ),
        );

        Ok(())
    }

    #[test]
    fn cut_at_unbounded_interval_exclusive_exclusive_cut() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            UnboundedInterval.cut_at(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            ),
            CutResult::Cut(
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToPast,
                )),
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                )),
            ),
        );

        Ok(())
    }

    #[test]
    fn cut_at_half_unbounded_interval() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            HalfBoundedAbsoluteInterval::new_from_time(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                OpeningDirection::ToFuture
            )
            .cut_at(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            ),
            CutResult::Cut(
                AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new_from_times_and_inclusivities(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                )),
                AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new_from_time_and_inclusivity(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    OpeningDirection::ToFuture,
                )),
            ),
        );

        Ok(())
    }

    #[test]
    fn cut_at_outside_before_bounded_interval() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_from_times(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )
            .cut_at(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            ),
            CutResult::Uncut,
        );

        Ok(())
    }

    #[test]
    fn cut_at_outside_after_bounded_interval() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_from_times(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )
            .cut_at(
                "2025-01-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Inclusive)
            ),
            CutResult::Uncut,
        );

        Ok(())
    }

    #[test]
    fn cut_at_inside_bounded_interval() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_from_times(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )
            .cut_at(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            ),
            CutResult::Cut(
                BoundedAbsoluteInterval::new_from_times_and_inclusivities(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                ),
                BoundedAbsoluteInterval::new_from_times_and_inclusivities(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
            ),
        );

        Ok(())
    }

    #[test]
    fn cut_at_inclusive_edge_bounded_interval() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_from_times(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            )
            .cut_at(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                CutType::new(BoundInclusivity::Inclusive, BoundInclusivity::Exclusive)
            ),
            CutResult::Cut(
                BoundedAbsoluteInterval::new_from_times_and_inclusivities(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
                BoundedAbsoluteInterval::new_from_times_and_inclusivities(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Inclusive,
                ),
            ),
        );

        Ok(())
    }

    #[test]
    fn cut_at_inclusive_edge_bounded_interval_would_create_illegal_interval() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_from_times(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
            )
            .cut_at(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            ),
            CutResult::Uncut,
        );

        Ok(())
    }

    #[test]
    fn cut_at_exclusive_edge_bounded_interval() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            BoundedAbsoluteInterval::new_from_times_and_inclusivities(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Inclusive,
            )
            .cut_at(
                "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Exclusive)
            ),
            CutResult::Uncut,
        );

        Ok(())
    }
}

use jiff::SignedDuration;

use super::abridge::*;
use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsStartBound,
    BoundedAbsInterval,
    EmptiableAbsBoundPair,
    HalfBoundedAbsInterval,
    HalfBoundedToFutureAbsInterval,
    HalfBoundedToPastAbsInterval,
};
use crate::intervals::meta::{BoundInclusivity, IntervalType, OpeningDirection};
use crate::intervals::relative::{
    BoundedRelInterval,
    EmptiableRelBoundPair,
    HalfBoundedRelInterval,
    HalfBoundedToFutureRelInterval,
    HalfBoundedToPastRelInterval,
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};
use crate::test_data::interval_overlap::{
    ABS_DATA,
    ABS_EMPTY_EMPTY_DATA,
    ABS_EMPTY_NONEMPTY_DATA,
    ABS_NONEMPTY_EMPTY_DATA,
    REL_DATA,
    REL_EMPTY_EMPTY_DATA,
    REL_EMPTY_NONEMPTY_DATA,
    REL_NONEMPTY_EMPTY_DATA,
};
use crate::test_utils::date_timestamp;

fn abs_assert(lhs: &AbsBoundPair, rhs: &EmptiableAbsBoundPair, expected: &EmptiableAbsBoundPair) {
    // Bound pair
    assert_eq!(lhs.clone().abridge(&rhs.clone()), expected.clone());
    // Emptiable bound pair
    assert_eq!(lhs.clone().to_emptiable().abridge(&rhs.clone()), expected.clone());
    // Interval
    assert_eq!(
        lhs.clone().to_interval().abridge(&rhs.clone().to_emptiable_interval()),
        expected.clone().to_emptiable_interval()
    );
    // Emptiable interval
    assert_eq!(
        lhs.clone()
            .to_emptiable_interval()
            .abridge(&rhs.clone().to_emptiable_interval()),
        expected.clone().to_emptiable_interval()
    );

    // Assertion for dedicated type has to be implemented individually as output type is unpredictable
}

fn abs_assert_empty(lhs: &EmptiableAbsBoundPair, rhs: &EmptiableAbsBoundPair, expected: &EmptiableAbsBoundPair) {
    // Emptiable bound pair
    assert_eq!(lhs.clone().abridge(&rhs.clone()), expected.clone());
    // Emptiable interval
    assert_eq!(
        lhs.clone()
            .to_emptiable_interval()
            .abridge(&rhs.clone().to_emptiable_interval()),
        expected.clone().to_emptiable_interval()
    );

    // Assertion for dedicated type has to be implemented individually as output type is unpredictable
}

fn rel_assert(lhs: &RelBoundPair, rhs: &EmptiableRelBoundPair, expected: &EmptiableRelBoundPair) {
    // Bound pair
    assert_eq!(lhs.clone().abridge(&rhs.clone()), expected.clone());
    // Emptiable bound pair
    assert_eq!(lhs.clone().to_emptiable().abridge(&rhs.clone()), expected.clone());
    // Interval
    assert_eq!(
        lhs.clone().to_interval().abridge(&rhs.clone().to_emptiable_interval()),
        expected.clone().to_emptiable_interval()
    );
    // Emptiable interval
    assert_eq!(
        lhs.clone()
            .to_emptiable_interval()
            .abridge(&rhs.clone().to_emptiable_interval()),
        expected.clone().to_emptiable_interval()
    );

    // Assertion for dedicated type has to be implemented individually as output type is unpredictable
}

fn rel_assert_empty(lhs: &EmptiableRelBoundPair, rhs: &EmptiableRelBoundPair, expected: &EmptiableRelBoundPair) {
    // Emptiable bound pair
    assert_eq!(lhs.clone().abridge(&rhs.clone()), expected.clone());
    // Emptiable interval
    assert_eq!(
        lhs.clone()
            .to_emptiable_interval()
            .abridge(&rhs.clone().to_emptiable_interval()),
        expected.clone().to_emptiable_interval()
    );

    // Assertion for dedicated type has to be implemented individually as output type is unpredictable
}

mod absolute {
    use super::*;

    mod bounded_bounded {
        use super::*;

        #[test]
        fn outside_before() {
            let data = ABS_DATA
                .get(&(IntervalType::Bounded, IntervalType::Bounded))
                .unwrap()
                .get("outside_before")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 3), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            abs_assert(
                &data.lhs().clone(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        #[test]
        fn outside_after() {
            let data = ABS_DATA
                .get(&(IntervalType::Bounded, IntervalType::Bounded))
                .unwrap()
                .get("outside_after")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 3), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            abs_assert(
                &data.lhs().clone(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("ends_on_start_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("ends_on_start_incl_excl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(&data.lhs().clone(), &data.rhs().clone().to_emptiable(), &expected);
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("ends_on_start_excl_incl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(&data.lhs().clone(), &data.rhs().clone().to_emptiable(), &expected);

                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("ends_on_start_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("starts_on_end_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("starts_on_end_incl_excl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(&data.lhs().clone(), &data.rhs().clone().to_emptiable(), &expected);
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("starts_on_end_excl_incl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(&data.lhs().clone(), &data.rhs().clone().to_emptiable(), &expected);
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("starts_on_end_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn crosses_start() {
            let data = ABS_DATA
                .get(&(IntervalType::Bounded, IntervalType::Bounded))
                .unwrap()
                .get("crosses_start")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            );

            abs_assert(
                &data.lhs().clone(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        #[test]
        fn crosses_end() {
            let data = ABS_DATA
                .get(&(IntervalType::Bounded, IntervalType::Bounded))
                .unwrap()
                .get("crosses_end")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            );

            abs_assert(
                &data.lhs().clone(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        #[test]
        fn inside() {
            let data = ABS_DATA
                .get(&(IntervalType::Bounded, IntervalType::Bounded))
                .unwrap()
                .get("inside")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            );

            abs_assert(
                &data.lhs().clone(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod inside_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_start_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_start_incl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_start_excl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_start_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        mod inside_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_end_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_end_incl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 3), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_end_excl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 3), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_end_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 3), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        mod equal {
            use super::*;

            #[test]
            fn start_inclusive_inclusive_end_inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_incl_end_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_inclusive_inclusive_end_inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_incl_end_incl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_inclusive_inclusive_end_exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_incl_end_excl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_inclusive_inclusive_end_exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_incl_end_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_inclusive_exclusive_end_inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_excl_end_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_inclusive_exclusive_end_inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_excl_end_incl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_inclusive_exclusive_end_exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_excl_end_excl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_inclusive_exclusive_end_exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_excl_end_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_inclusive_end_inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_incl_end_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_inclusive_end_inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_incl_end_incl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_inclusive_end_exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_incl_end_excl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_inclusive_end_exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_incl_end_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_exclusive_end_inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_excl_end_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_exclusive_end_inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_excl_end_incl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_exclusive_end_exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_excl_end_excl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_exclusive_end_exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_excl_end_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        mod contains_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_start_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_start_incl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_start_excl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_start_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        mod contains_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_end_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_end_incl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 3), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_end_excl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 3), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_end_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 3), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn contains() {
            let data = ABS_DATA
                .get(&(IntervalType::Bounded, IntervalType::Bounded))
                .unwrap()
                .get("contains")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            );

            abs_assert(
                &data.lhs().clone(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }
    }

    mod bounded_half_bounded_to_future {
        use super::*;

        #[test]
        fn outside_before() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::Bounded,
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("outside_before")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 3), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_incl_excl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_excl_incl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn crosses_start() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::Bounded,
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("crosses_start")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        #[test]
        fn inside() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::Bounded,
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("inside")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod inside_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("inside_and_same_start_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("inside_and_same_start_incl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("inside_and_same_start_excl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("inside_and_same_start_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }
    }

    mod bounded_half_bounded_to_past {
        use super::*;

        #[test]
        fn outside_after() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::Bounded,
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("outside_after")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_incl_excl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_excl_incl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn crosses_end() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::Bounded,
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("crosses_end")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        #[test]
        fn inside() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::Bounded,
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("inside")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod inside_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("inside_and_same_end_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("inside_and_same_end_incl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("inside_and_same_end_excl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("inside_and_same_end_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }
    }

    mod bounded_unbounded {
        use super::*;

        #[test]
        fn inside() {
            let data = ABS_DATA
                .get(&(IntervalType::Bounded, IntervalType::Unbounded))
                .unwrap()
                .get("inside")
                .unwrap();

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.lhs().clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&UnboundedInterval::try_from(data.rhs().clone()).unwrap()),
                BoundedAbsInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod bounded_empty {
        use super::*;

        #[test]
        fn outside() {
            let data = ABS_NONEMPTY_EMPTY_DATA.get("bounded_outside").unwrap();

            abs_assert(data.lhs(), data.rhs(), &data.lhs().clone().to_emptiable());
            assert_eq!(
                BoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&EmptyInterval::try_from(data.rhs().clone()).unwrap()),
                BoundedAbsInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod half_bounded_to_future_bounded {
        use super::*;

        #[test]
        fn outside_after() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::Bounded,
                ))
                .unwrap()
                .get("outside_after")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 3), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("starts_on_end_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("starts_on_end_incl_excl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("starts_on_end_excl_incl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("starts_on_end_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn crosses_end() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::Bounded,
                ))
                .unwrap()
                .get("crosses_end")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod contains_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_start_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_start_incl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_start_excl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_start_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn contains() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::Bounded,
                ))
                .unwrap()
                .get("contains")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 3)).to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }
    }

    mod half_bounded_to_future_half_bounded_to_future {
        use super::*;

        #[test]
        fn inside_and_same_end() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("inside_and_same_end")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod equal {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("equal_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("equal_incl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("equal_excl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("equal_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    AbsEndBound::InfiniteFuture,
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn contains_and_same_end() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("contains_and_same_end")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_start_bound(),
                AbsEndBound::InfiniteFuture,
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }
    }

    mod half_bounded_to_future_half_bounded_to_past {
        use super::*;

        #[test]
        fn outside_after() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("outside_after")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_incl_excl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_excl_incl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn crosses_end() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("crosses_end")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }
    }

    mod half_bounded_to_future_unbounded {
        use super::*;

        #[test]
        fn inside_and_same_end() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::Unbounded,
                ))
                .unwrap()
                .get("inside_and_same_end")
                .unwrap();

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.lhs().clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&UnboundedInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone()).unwrap()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&UnboundedInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedAbsInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod half_bounded_to_future_empty {
        use super::*;

        #[test]
        fn outside() {
            let data = ABS_NONEMPTY_EMPTY_DATA.get("half_bounded_to_future_outside").unwrap();

            abs_assert(data.lhs(), data.rhs(), &data.lhs().clone().to_emptiable());
            assert_eq!(
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&EmptyInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToFutureAbsInterval::try_from(data.lhs().clone()).unwrap()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&EmptyInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedAbsInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod half_bounded_to_past_bounded {
        use super::*;

        #[test]
        fn outside_before() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::Bounded,
                ))
                .unwrap()
                .get("outside_before")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("ends_on_start_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("ends_on_start_incl_excl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("ends_on_start_excl_incl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("ends_on_start_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn crosses_start() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::Bounded,
                ))
                .unwrap()
                .get("crosses_start")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod contains_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_end_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_end_incl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_end_excl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_end_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn contains() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::Bounded,
                ))
                .unwrap()
                .get("contains")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }
    }

    mod half_bounded_to_past_half_bounded_to_future {
        use super::*;

        #[test]
        fn outside_before() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("outside_before")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 2), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_incl_excl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected);
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_excl_incl")
                    .unwrap();

                let expected = EmptiableAbsBoundPair::Empty;

                abs_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected);
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn crosses_start() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("crosses_start")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_start_bound(),
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 2)).to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }
    }

    mod half_bounded_to_past_half_bounded_to_past {
        use super::*;

        #[test]
        fn inside_and_same_start() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("inside_and_same_start")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod equal {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("equal_incl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("equal_incl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("equal_excl_incl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = ABS_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("equal_excl_excl")
                    .unwrap();

                let expected = AbsBoundPair::new(
                    AbsStartBound::InfinitePast,
                    AbsFiniteBoundPos::new_with_incl(date_timestamp(2026, 1, 1), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                abs_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedAbsInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn contains_and_same_start() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("contains_and_same_start")
                .unwrap();

            let expected = AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new(date_timestamp(2026, 1, 1)).to_end_bound(),
            );

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }
    }

    mod half_bounded_to_past_unbounded {
        use super::*;

        #[test]
        fn inside_and_same_start() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::Unbounded,
                ))
                .unwrap()
                .get("inside_and_same_start")
                .unwrap();

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.lhs().clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&UnboundedInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone()).unwrap()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&UnboundedInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedAbsInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod half_bounded_to_past_empty {
        use super::*;

        #[test]
        fn outside() {
            let data = ABS_NONEMPTY_EMPTY_DATA.get("half_bounded_to_past_outside").unwrap();

            abs_assert(data.lhs(), data.rhs(), &data.lhs().clone().to_emptiable());
            assert_eq!(
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&EmptyInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToPastAbsInterval::try_from(data.lhs().clone()).unwrap()
            );
            assert_eq!(
                HalfBoundedAbsInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&EmptyInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedAbsInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod unbounded_bounded {
        use super::*;

        #[test]
        fn contains() {
            let data = ABS_DATA
                .get(&(IntervalType::Unbounded, IntervalType::Bounded))
                .unwrap()
                .get("contains")
                .unwrap();

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.rhs().clone().to_emptiable(),
            );
            assert_eq!(
                UnboundedInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()
            );
        }
    }

    mod unbounded_half_bounded_to_future {
        use super::*;

        #[test]
        fn contains_and_same_end() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::Unbounded,
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("contains_and_same_end")
                .unwrap();

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.rhs().clone().to_emptiable(),
            );
            assert_eq!(
                UnboundedInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()
            );
            assert_eq!(
                UnboundedInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()
            );
        }
    }

    mod unbounded_half_bounded_to_past {
        use super::*;

        #[test]
        fn contains_and_same_start() {
            let data = ABS_DATA
                .get(&(
                    IntervalType::Unbounded,
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("contains_and_same_start")
                .unwrap();

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.rhs().clone().to_emptiable(),
            );
            assert_eq!(
                UnboundedInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()
            );
            assert_eq!(
                UnboundedInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()
            );
        }
    }

    mod unbounded_unbounded {
        use super::*;

        #[test]
        fn equal() {
            let data = ABS_DATA
                .get(&(IntervalType::Unbounded, IntervalType::Unbounded))
                .unwrap()
                .get("equal")
                .unwrap();

            abs_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.lhs().clone().to_emptiable(),
            );
            assert_eq!(
                UnboundedInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&UnboundedInterval::try_from(data.rhs().clone()).unwrap()),
                UnboundedInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod unbounded_empty {
        use super::*;

        #[test]
        fn outside() {
            let data = ABS_NONEMPTY_EMPTY_DATA.get("unbounded_outside").unwrap();

            abs_assert(data.lhs(), data.rhs(), &data.lhs().clone().to_emptiable());
            assert_eq!(
                UnboundedInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&EmptyInterval::try_from(data.rhs().clone()).unwrap()),
                UnboundedInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod empty_bounded {
        use super::*;

        #[test]
        fn outside() {
            let data = ABS_EMPTY_NONEMPTY_DATA.get("bounded_outside").unwrap();

            abs_assert_empty(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.rhs().clone().to_emptiable(),
            );
            assert_eq!(
                EmptyInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                BoundedAbsInterval::try_from(data.rhs().clone()).unwrap()
            );
        }
    }

    mod empty_half_bounded_to_future {
        use super::*;

        #[test]
        fn outside() {
            let data = ABS_EMPTY_NONEMPTY_DATA.get("half_bounded_to_future_outside").unwrap();

            abs_assert_empty(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.rhs().clone().to_emptiable(),
            );
            assert_eq!(
                EmptyInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToFutureAbsInterval::try_from(data.rhs().clone()).unwrap()
            );
            assert_eq!(
                EmptyInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()
            );
        }
    }

    mod empty_half_bounded_to_past {
        use super::*;

        #[test]
        fn outside_to_past() {
            let data = ABS_EMPTY_NONEMPTY_DATA.get("half_bounded_to_past_outside").unwrap();

            abs_assert_empty(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.rhs().clone().to_emptiable(),
            );
            assert_eq!(
                EmptyInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToPastAbsInterval::try_from(data.rhs().clone()).unwrap()
            );
            assert_eq!(
                EmptyInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedAbsInterval::try_from(data.rhs().clone()).unwrap()
            );
        }
    }

    mod empty_unbounded {
        use super::*;

        #[test]
        fn outside() {
            let data = ABS_EMPTY_NONEMPTY_DATA.get("unbounded_outside").unwrap();

            abs_assert_empty(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.rhs().clone().to_emptiable(),
            );
            assert_eq!(
                EmptyInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&UnboundedInterval::try_from(data.rhs().clone()).unwrap()),
                UnboundedInterval::try_from(data.rhs().clone()).unwrap()
            );
        }
    }

    mod empty_empty {
        use super::*;

        #[test]
        fn outside() {
            abs_assert_empty(
                ABS_EMPTY_EMPTY_DATA.lhs(),
                ABS_EMPTY_EMPTY_DATA.rhs(),
                &ABS_EMPTY_EMPTY_DATA.lhs().clone(),
            );
            assert_eq!(
                EmptyInterval::try_from(ABS_EMPTY_EMPTY_DATA.lhs().clone())
                    .unwrap()
                    .abridge(&EmptyInterval::try_from(ABS_EMPTY_EMPTY_DATA.rhs().clone()).unwrap()),
                EmptyInterval::try_from(ABS_EMPTY_EMPTY_DATA.lhs().clone()).unwrap()
            );
        }
    }
}

mod relative {
    use super::*;

    mod bounded_bounded {
        use super::*;

        #[test]
        fn outside_before() {
            let data = REL_DATA
                .get(&(IntervalType::Bounded, IntervalType::Bounded))
                .unwrap()
                .get("outside_before")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(3), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                &data.lhs().clone(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        #[test]
        fn outside_after() {
            let data = REL_DATA
                .get(&(IntervalType::Bounded, IntervalType::Bounded))
                .unwrap()
                .get("outside_after")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(3), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                &data.lhs().clone(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("ends_on_start_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("ends_on_start_incl_excl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(&data.lhs().clone(), &data.rhs().clone().to_emptiable(), &expected);
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("ends_on_start_excl_incl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(&data.lhs().clone(), &data.rhs().clone().to_emptiable(), &expected);

                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("ends_on_start_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("starts_on_end_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("starts_on_end_incl_excl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(&data.lhs().clone(), &data.rhs().clone().to_emptiable(), &expected);
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("starts_on_end_excl_incl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(&data.lhs().clone(), &data.rhs().clone().to_emptiable(), &expected);
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("starts_on_end_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn crosses_start() {
            let data = REL_DATA
                .get(&(IntervalType::Bounded, IntervalType::Bounded))
                .unwrap()
                .get("crosses_start")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            );

            rel_assert(
                &data.lhs().clone(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        #[test]
        fn crosses_end() {
            let data = REL_DATA
                .get(&(IntervalType::Bounded, IntervalType::Bounded))
                .unwrap()
                .get("crosses_end")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            );

            rel_assert(
                &data.lhs().clone(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        #[test]
        fn inside() {
            let data = REL_DATA
                .get(&(IntervalType::Bounded, IntervalType::Bounded))
                .unwrap()
                .get("inside")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            );

            rel_assert(
                &data.lhs().clone(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod inside_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_start_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_start_incl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_start_excl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_start_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        mod inside_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_end_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_end_incl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(3), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_end_excl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(3), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("inside_and_same_end_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(3), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        mod equal {
            use super::*;

            #[test]
            fn start_inclusive_inclusive_end_inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_incl_end_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_inclusive_inclusive_end_inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_incl_end_incl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_inclusive_inclusive_end_exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_incl_end_excl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_inclusive_inclusive_end_exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_incl_end_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_inclusive_exclusive_end_inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_excl_end_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_inclusive_exclusive_end_inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_excl_end_incl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_inclusive_exclusive_end_exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_excl_end_excl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_inclusive_exclusive_end_exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_incl_excl_end_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_inclusive_end_inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_incl_end_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_inclusive_end_inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_incl_end_incl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_inclusive_end_exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_incl_end_excl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_inclusive_end_exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_incl_end_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_exclusive_end_inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_excl_end_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_exclusive_end_inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_excl_end_incl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_exclusive_end_exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_excl_end_excl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn start_exclusive_exclusive_end_exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("equal_start_excl_excl_end_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        mod contains_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_start_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_start_incl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_start_excl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_start_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        mod contains_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_end_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_end_incl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(3), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_end_excl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(3), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(IntervalType::Bounded, IntervalType::Bounded))
                    .unwrap()
                    .get("contains_and_same_end_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(3), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    &data.lhs().clone(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn contains() {
            let data = REL_DATA
                .get(&(IntervalType::Bounded, IntervalType::Bounded))
                .unwrap()
                .get("contains")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            );

            rel_assert(
                &data.lhs().clone(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }
    }

    mod bounded_half_bounded_to_future {
        use super::*;

        #[test]
        fn outside_before() {
            let data = REL_DATA
                .get(&(
                    IntervalType::Bounded,
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("outside_before")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(3), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_incl_excl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_excl_incl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn crosses_start() {
            let data = REL_DATA
                .get(&(
                    IntervalType::Bounded,
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("crosses_start")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        #[test]
        fn inside() {
            let data = REL_DATA
                .get(&(
                    IntervalType::Bounded,
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("inside")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod inside_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("inside_and_same_start_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("inside_and_same_start_incl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("inside_and_same_start_excl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("inside_and_same_start_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }
    }

    mod bounded_half_bounded_to_past {
        use super::*;

        #[test]
        fn outside_after() {
            let data = REL_DATA
                .get(&(
                    IntervalType::Bounded,
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("outside_after")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_incl_excl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_excl_incl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn crosses_end() {
            let data = REL_DATA
                .get(&(
                    IntervalType::Bounded,
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("crosses_end")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        #[test]
        fn inside() {
            let data = REL_DATA
                .get(&(
                    IntervalType::Bounded,
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("inside")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod inside_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("inside_and_same_end_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("inside_and_same_end_incl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("inside_and_same_end_excl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::Bounded,
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("inside_and_same_end_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    BoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }
    }

    mod bounded_unbounded {
        use super::*;

        #[test]
        fn inside() {
            let data = REL_DATA
                .get(&(IntervalType::Bounded, IntervalType::Unbounded))
                .unwrap()
                .get("inside")
                .unwrap();

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.lhs().clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&UnboundedInterval::try_from(data.rhs().clone()).unwrap()),
                BoundedRelInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod bounded_empty {
        use super::*;

        #[test]
        fn outside() {
            let data = REL_NONEMPTY_EMPTY_DATA.get("bounded_outside").unwrap();

            rel_assert(data.lhs(), data.rhs(), &data.lhs().clone().to_emptiable());
            assert_eq!(
                BoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&EmptyInterval::try_from(data.rhs().clone()).unwrap()),
                BoundedRelInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod half_bounded_to_future_bounded {
        use super::*;

        #[test]
        fn outside_after() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::Bounded,
                ))
                .unwrap()
                .get("outside_after")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(3), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("starts_on_end_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("starts_on_end_incl_excl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("starts_on_end_excl_incl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("starts_on_end_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn crosses_end() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::Bounded,
                ))
                .unwrap()
                .get("crosses_end")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod contains_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_start_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_start_incl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_start_excl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_start_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn contains() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::Bounded,
                ))
                .unwrap()
                .get("contains")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }
    }

    mod half_bounded_to_future_half_bounded_to_future {
        use super::*;

        #[test]
        fn inside_and_same_end() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("inside_and_same_end")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod equal {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("equal_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelEndBound::InfiniteFuture,
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("equal_incl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelEndBound::InfiniteFuture,
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("equal_excl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelEndBound::InfiniteFuture,
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("equal_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_start_bound(),
                    RelEndBound::InfiniteFuture,
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn contains_and_same_end() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("contains_and_same_end")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelEndBound::InfiniteFuture,
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }
    }

    mod half_bounded_to_future_half_bounded_to_past {
        use super::*;

        #[test]
        fn outside_after() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("outside_after")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_incl_excl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_excl_incl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("starts_on_end_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn crosses_end() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("crosses_end")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }
    }

    mod half_bounded_to_future_unbounded {
        use super::*;

        #[test]
        fn inside_and_same_end() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    IntervalType::Unbounded,
                ))
                .unwrap()
                .get("inside_and_same_end")
                .unwrap();

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.lhs().clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&UnboundedInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone()).unwrap()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&UnboundedInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedRelInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod half_bounded_to_future_empty {
        use super::*;

        #[test]
        fn outside() {
            let data = REL_NONEMPTY_EMPTY_DATA.get("half_bounded_to_future_outside").unwrap();

            rel_assert(data.lhs(), data.rhs(), &data.lhs().clone().to_emptiable());
            assert_eq!(
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&EmptyInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToFutureRelInterval::try_from(data.lhs().clone()).unwrap()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&EmptyInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedRelInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod half_bounded_to_past_bounded {
        use super::*;

        #[test]
        fn outside_before() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::Bounded,
                ))
                .unwrap()
                .get("outside_before")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("ends_on_start_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("ends_on_start_incl_excl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("ends_on_start_excl_incl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("ends_on_start_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn crosses_start() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::Bounded,
                ))
                .unwrap()
                .get("crosses_start")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod contains_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_end_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_end_incl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_end_excl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::Bounded,
                    ))
                    .unwrap()
                    .get("contains_and_same_end_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn contains() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::Bounded,
                ))
                .unwrap()
                .get("contains")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }
    }

    mod half_bounded_to_past_half_bounded_to_future {
        use super::*;

        #[test]
        fn outside_before() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("outside_before")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_incl_excl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected);
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_excl_incl")
                    .unwrap();

                let expected = EmptiableRelBoundPair::Empty;

                rel_assert(data.lhs(), &data.rhs().clone().to_emptiable(), &expected);
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToFuture),
                    ))
                    .unwrap()
                    .get("ends_on_start_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn crosses_start() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("crosses_start")
                .unwrap();

            let expected = RelBoundPair::new(
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelFiniteBoundPos::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }
    }

    mod half_bounded_to_past_half_bounded_to_past {
        use super::*;

        #[test]
        fn inside_and_same_start() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("inside_and_same_start")
                .unwrap();

            let expected = RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }

        mod equal {
            use super::*;

            #[test]
            fn inclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("equal_incl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn inclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("equal_incl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_inclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("equal_excl_incl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }

            #[test]
            fn exclusive_exclusive() {
                let data = REL_DATA
                    .get(&(
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                        IntervalType::HalfBounded(OpeningDirection::ToPast),
                    ))
                    .unwrap()
                    .get("equal_excl_excl")
                    .unwrap();

                let expected = RelBoundPair::new(
                    RelStartBound::InfinitePast,
                    RelFiniteBoundPos::new_with_incl(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                        .to_end_bound(),
                );

                rel_assert(
                    data.lhs(),
                    &data.rhs().clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
                assert_eq!(
                    HalfBoundedRelInterval::try_from(data.lhs().clone())
                        .unwrap()
                        .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                    expected.clone().to_emptiable_interval()
                );
            }
        }

        #[test]
        fn contains_and_same_start() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("contains_and_same_start")
                .unwrap();

            let expected = RelBoundPair::new(
                RelStartBound::InfinitePast,
                RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
            );

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                expected.clone().to_emptiable_interval()
            );
        }
    }

    mod half_bounded_to_past_unbounded {
        use super::*;

        #[test]
        fn inside_and_same_start() {
            let data = REL_DATA
                .get(&(
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                    IntervalType::Unbounded,
                ))
                .unwrap()
                .get("inside_and_same_start")
                .unwrap();

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.lhs().clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&UnboundedInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone()).unwrap()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&UnboundedInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedRelInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod half_bounded_to_past_empty {
        use super::*;

        #[test]
        fn outside() {
            let data = REL_NONEMPTY_EMPTY_DATA.get("half_bounded_to_past_outside").unwrap();

            rel_assert(data.lhs(), data.rhs(), &data.lhs().clone().to_emptiable());
            assert_eq!(
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&EmptyInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToPastRelInterval::try_from(data.lhs().clone()).unwrap()
            );
            assert_eq!(
                HalfBoundedRelInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&EmptyInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedRelInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod unbounded_bounded {
        use super::*;

        #[test]
        fn contains() {
            let data = REL_DATA
                .get(&(IntervalType::Unbounded, IntervalType::Bounded))
                .unwrap()
                .get("contains")
                .unwrap();

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.rhs().clone().to_emptiable(),
            );
            assert_eq!(
                UnboundedInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                BoundedRelInterval::try_from(data.rhs().clone()).unwrap()
            );
        }
    }

    mod unbounded_half_bounded_to_future {
        use super::*;

        #[test]
        fn contains_and_same_end() {
            let data = REL_DATA
                .get(&(
                    IntervalType::Unbounded,
                    IntervalType::HalfBounded(OpeningDirection::ToFuture),
                ))
                .unwrap()
                .get("contains_and_same_end")
                .unwrap();

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.rhs().clone().to_emptiable(),
            );
            assert_eq!(
                UnboundedInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()
            );
            assert_eq!(
                UnboundedInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()
            );
        }
    }

    mod unbounded_half_bounded_to_past {
        use super::*;

        #[test]
        fn contains_and_same_start() {
            let data = REL_DATA
                .get(&(
                    IntervalType::Unbounded,
                    IntervalType::HalfBounded(OpeningDirection::ToPast),
                ))
                .unwrap()
                .get("contains_and_same_start")
                .unwrap();

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.rhs().clone().to_emptiable(),
            );
            assert_eq!(
                UnboundedInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()
            );
            assert_eq!(
                UnboundedInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()
            );
        }
    }

    mod unbounded_unbounded {
        use super::*;

        #[test]
        fn equal() {
            let data = REL_DATA
                .get(&(IntervalType::Unbounded, IntervalType::Unbounded))
                .unwrap()
                .get("equal")
                .unwrap();

            rel_assert(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.lhs().clone().to_emptiable(),
            );
            assert_eq!(
                UnboundedInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&UnboundedInterval::try_from(data.rhs().clone()).unwrap()),
                UnboundedInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod unbounded_empty {
        use super::*;

        #[test]
        fn outside() {
            let data = REL_NONEMPTY_EMPTY_DATA.get("unbounded_outside").unwrap();

            rel_assert(data.lhs(), data.rhs(), &data.lhs().clone().to_emptiable());
            assert_eq!(
                UnboundedInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&EmptyInterval::try_from(data.rhs().clone()).unwrap()),
                UnboundedInterval::try_from(data.lhs().clone()).unwrap()
            );
        }
    }

    mod empty_bounded {
        use super::*;

        #[test]
        fn outside() {
            let data = REL_EMPTY_NONEMPTY_DATA.get("bounded_outside").unwrap();

            rel_assert_empty(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.rhs().clone().to_emptiable(),
            );
            assert_eq!(
                EmptyInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&BoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                BoundedRelInterval::try_from(data.rhs().clone()).unwrap()
            );
        }
    }

    mod empty_half_bounded_to_future {
        use super::*;

        #[test]
        fn outside() {
            let data = REL_EMPTY_NONEMPTY_DATA.get("half_bounded_to_future_outside").unwrap();

            rel_assert_empty(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.rhs().clone().to_emptiable(),
            );
            assert_eq!(
                EmptyInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToFutureRelInterval::try_from(data.rhs().clone()).unwrap()
            );
            assert_eq!(
                EmptyInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()
            );
        }
    }

    mod empty_half_bounded_to_past {
        use super::*;

        #[test]
        fn outside_to_past() {
            let data = REL_EMPTY_NONEMPTY_DATA.get("half_bounded_to_past_outside").unwrap();

            rel_assert_empty(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.rhs().clone().to_emptiable(),
            );
            assert_eq!(
                EmptyInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedToPastRelInterval::try_from(data.rhs().clone()).unwrap()
            );
            assert_eq!(
                EmptyInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()),
                HalfBoundedRelInterval::try_from(data.rhs().clone()).unwrap()
            );
        }
    }

    mod empty_unbounded {
        use super::*;

        #[test]
        fn outside() {
            let data = REL_EMPTY_NONEMPTY_DATA.get("unbounded_outside").unwrap();

            rel_assert_empty(
                data.lhs(),
                &data.rhs().clone().to_emptiable(),
                &data.rhs().clone().to_emptiable(),
            );
            assert_eq!(
                EmptyInterval::try_from(data.lhs().clone())
                    .unwrap()
                    .abridge(&UnboundedInterval::try_from(data.rhs().clone()).unwrap()),
                UnboundedInterval::try_from(data.rhs().clone()).unwrap()
            );
        }
    }

    mod empty_empty {
        use super::*;

        #[test]
        fn outside() {
            rel_assert_empty(
                REL_EMPTY_EMPTY_DATA.lhs(),
                REL_EMPTY_EMPTY_DATA.rhs(),
                &REL_EMPTY_EMPTY_DATA.lhs().clone(),
            );
            assert_eq!(
                EmptyInterval::try_from(REL_EMPTY_EMPTY_DATA.lhs().clone())
                    .unwrap()
                    .abridge(&EmptyInterval::try_from(REL_EMPTY_EMPTY_DATA.rhs().clone()).unwrap()),
                EmptyInterval::try_from(REL_EMPTY_EMPTY_DATA.lhs().clone()).unwrap()
            );
        }
    }
}

mod special {
    use super::*;

    mod unbounded_unbounded {
        use super::*;

        #[test]
        fn equal() {
            assert_eq!(UnboundedInterval.abridge(&UnboundedInterval), UnboundedInterval);
        }
    }

    mod unbounded_empty {
        use super::*;

        #[test]
        fn outside() {
            assert_eq!(UnboundedInterval.abridge(&EmptyInterval), UnboundedInterval);
        }
    }

    mod empty_unbounded {
        use super::*;

        #[test]
        fn outside() {
            assert_eq!(EmptyInterval.abridge(&UnboundedInterval), UnboundedInterval);
        }
    }

    mod empty_empty {
        use super::*;

        #[test]
        fn outside() {
            assert_eq!(EmptyInterval.abridge(&EmptyInterval), EmptyInterval);
        }
    }
}

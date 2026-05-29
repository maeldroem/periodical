use std::error::Error;

use jiff::{SignedDuration, Timestamp};

use super::abridge::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteStartBound,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
    HasEmptiableAbsoluteBoundPair,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::test_data::{
    BOUNDED_BOUNDED_ABS,
    BOUNDED_BOUNDED_REL,
    BOUNDED_HALF_BOUNDED_ABS,
    BOUNDED_HALF_BOUNDED_REL,
    HALF_BOUNDED_BOUNDED_ABS,
    HALF_BOUNDED_BOUNDED_REL,
    HALF_BOUNDED_HALF_BOUNDED_ABS,
    HALF_BOUNDED_HALF_BOUNDED_REL,
};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    EmptiableRelativeBoundPair,
    HalfBoundedRelativeInterval,
    HasEmptiableRelativeBoundPair,
    HasRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBoundPosition,
    RelativeStartBound,
};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

fn abs_assert(lhs: &AbsoluteBoundPair, rhs: &EmptiableAbsoluteBoundPair, expected: &EmptiableAbsoluteBoundPair) {
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

fn abs_assert_empty(
    lhs: &EmptiableAbsoluteBoundPair,
    rhs: &EmptiableAbsoluteBoundPair,
    expected: &EmptiableAbsoluteBoundPair,
) {
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

fn rel_assert(lhs: &RelativeBoundPair, rhs: &EmptiableRelativeBoundPair, expected: &EmptiableRelativeBoundPair) {
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

fn rel_assert_empty(
    lhs: &EmptiableRelativeBoundPair,
    rhs: &EmptiableRelativeBoundPair,
    expected: &EmptiableRelativeBoundPair,
) {
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
        fn outside_before() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_ABS
                .as_ref()?
                .get("outside_before")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn outside_after() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_ABS
                .as_ref()?
                .get("outside_after")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());

                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        #[test]
        fn crosses_start() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_ABS
                .as_ref()?
                .get("crosses_start")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn crosses_end() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_ABS
                .as_ref()?
                .get("crosses_end")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn inside() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_ABS
                .as_ref()?
                .get("inside")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod inside_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod inside_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod equal {
            use super::*;

            #[test]
            fn start_inclusive_inclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_incl_incl_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_inclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_incl_incl_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_inclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_incl_incl_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_inclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_incl_incl_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_exclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_incl_excl_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_exclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_incl_excl_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_exclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_incl_excl_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_exclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_incl_excl_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_inclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_excl_incl_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_inclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_excl_incl_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_inclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_excl_incl_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_inclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_excl_incl_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_exclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_excl_excl_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_exclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_excl_excl_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_exclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_excl_excl_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_exclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("equal_start_excl_excl_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod contains_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod contains_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        #[test]
        fn contains() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_ABS
                .as_ref()?
                .get("contains")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }
    }

    mod bounded_half_bounded {
        use super::*;

        #[test]
        fn outside_before() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_HALF_BOUNDED_ABS
                .as_ref()?
                .get("outside_before")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn outside_after() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_HALF_BOUNDED_ABS
                .as_ref()?
                .get("outside_after")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        #[test]
        fn crosses_start() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_HALF_BOUNDED_ABS
                .as_ref()?
                .get("crosses_start")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn crosses_end() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_HALF_BOUNDED_ABS
                .as_ref()?
                .get("crosses_end")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod inside {
            use super::*;

            #[test]
            fn to_future() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_to_future")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn to_past() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_to_past")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod inside_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod inside_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("inside_and_same_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }
    }

    mod bounded_unbounded {
        use super::*;

        #[test]
        fn inside() -> Result<(), Box<dyn Error>> {
            let bounded = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &bounded.clone(),
                &UnboundedInterval.emptiable_abs_bound_pair(),
                &bounded.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsoluteInterval::try_from(bounded.clone())?.abridge(&UnboundedInterval),
                BoundedAbsoluteInterval::try_from(bounded.clone())?
            );

            Ok(())
        }
    }

    mod bounded_empty {
        use super::*;

        #[test]
        fn outside() -> Result<(), Box<dyn Error>> {
            let bounded = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &bounded.clone(),
                &EmptiableAbsoluteBoundPair::Empty,
                &bounded.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedAbsoluteInterval::try_from(bounded.clone())?.abridge(&EmptyInterval),
                BoundedAbsoluteInterval::try_from(bounded.clone())?
            );

            Ok(())
        }
    }

    mod half_bounded_bounded {
        use super::*;

        #[test]
        fn outside_before() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_BOUNDED_ABS
                .as_ref()?
                .get("outside_before")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn outside_after() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_BOUNDED_ABS
                .as_ref()?
                .get("outside_after")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        #[test]
        fn crosses_start() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_BOUNDED_ABS
                .as_ref()?
                .get("crosses_start")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn crosses_end() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_BOUNDED_ABS
                .as_ref()?
                .get("crosses_end")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod contains_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod contains_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_and_same_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod contains {
            use super::*;

            #[test]
            fn to_future() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_to_future")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn to_past() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_ABS
                    .as_ref()?
                    .get("contains_to_past")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&BoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }
    }

    mod half_bounded_half_bounded {
        use super::*;

        #[test]
        fn outside_before() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                .as_ref()?
                .get("outside_before")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn outside_after() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                .as_ref()?
                .get("outside_after")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("ends_on_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableAbsoluteBoundPair::Empty;

                abs_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                    .as_ref()?
                    .get("starts_on_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = AbsoluteBoundPair::new(
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                );

                abs_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        #[test]
        fn crosses_start() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                .as_ref()?
                .get("crosses_start")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn crosses_end() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                .as_ref()?
                .get("crosses_end")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn inside_and_same_start() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                .as_ref()?
                .get("inside_and_same_start")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn inside_and_same_end() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                .as_ref()?
                .get("inside_and_same_end")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod equal {
            use super::*;

            mod to_future {
                use super::*;

                #[test]
                fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                        .as_ref()?
                        .get("equal_to_future_incl_incl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    );

                    abs_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }

                #[test]
                fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                        .as_ref()?
                        .get("equal_to_future_incl_excl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    );

                    abs_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }

                #[test]
                fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                        .as_ref()?
                        .get("equal_to_future_excl_incl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    );

                    abs_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }

                #[test]
                fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                        .as_ref()?
                        .get("equal_to_future_excl_excl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = AbsoluteBoundPair::new(
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteEndBound::InfiniteFuture,
                    );

                    abs_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }
            }

            mod to_past {
                use super::*;

                #[test]
                fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                        .as_ref()?
                        .get("equal_to_past_incl_incl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    );

                    abs_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }

                #[test]
                fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                        .as_ref()?
                        .get("equal_to_past_incl_excl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    );

                    abs_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }

                #[test]
                fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                        .as_ref()?
                        .get("equal_to_past_excl_incl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    );

                    abs_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }

                #[test]
                fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                        .as_ref()?
                        .get("equal_to_past_excl_excl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = AbsoluteBoundPair::new(
                        AbsoluteStartBound::InfinitePast,
                        AbsoluteFiniteBoundPosition::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    );

                    abs_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }
            }
        }

        #[test]
        fn contains_and_same_start() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                .as_ref()?
                .get("contains_and_same_start")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn contains_and_same_end() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_ABS
                .as_ref()?
                .get("contains_and_same_end")
                .cloned()
                .ok_or("data not found")?;

            let expected = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            );

            abs_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedAbsoluteInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }
    }

    mod half_bounded_unbounded {
        use super::*;

        #[test]
        fn inside_and_same_start() -> Result<(), Box<dyn Error>> {
            let half_bounded = AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &half_bounded.clone(),
                &UnboundedInterval.emptiable_abs_bound_pair(),
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?.abridge(&UnboundedInterval),
                HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }

        #[test]
        fn inside_and_same_end() -> Result<(), Box<dyn Error>> {
            let half_bounded = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            );

            abs_assert(
                &half_bounded.clone(),
                &UnboundedInterval.emptiable_abs_bound_pair(),
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?.abridge(&UnboundedInterval),
                HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }
    }

    mod half_bounded_empty {
        use super::*;

        #[test]
        fn outside_to_past() -> Result<(), Box<dyn Error>> {
            let half_bounded = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            );

            abs_assert(
                &half_bounded.clone(),
                &EmptiableAbsoluteBoundPair::Empty,
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?.abridge(&EmptyInterval),
                HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }

        #[test]
        fn outside_to_future() -> Result<(), Box<dyn Error>> {
            let half_bounded = AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &half_bounded.clone(),
                &EmptiableAbsoluteBoundPair::Empty,
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?.abridge(&EmptyInterval),
                HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }
    }

    mod unbounded_bounded {
        use super::*;

        #[test]
        fn contains() -> Result<(), Box<dyn Error>> {
            let bounded = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &UnboundedInterval.abs_bound_pair(),
                &bounded.clone().to_emptiable(),
                &bounded.clone().to_emptiable(),
            );
            assert_eq!(
                UnboundedInterval.abridge(&BoundedAbsoluteInterval::try_from(bounded.clone())?),
                BoundedAbsoluteInterval::try_from(bounded.clone())?
            );

            Ok(())
        }
    }

    mod unbounded_half_bounded {
        use super::*;

        #[test]
        fn contains_and_same_start() -> Result<(), Box<dyn Error>> {
            let half_bounded = AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert(
                &UnboundedInterval.abs_bound_pair(),
                &half_bounded.clone().to_emptiable(),
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                UnboundedInterval.abridge(&HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?),
                HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }

        #[test]
        fn contains_and_same_end() -> Result<(), Box<dyn Error>> {
            let half_bounded = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            );

            abs_assert(
                &UnboundedInterval.abs_bound_pair(),
                &half_bounded.clone().to_emptiable(),
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                UnboundedInterval.abridge(&HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?),
                HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }
    }

    mod unbounded_unbounded {
        use super::*;

        #[test]
        fn equal() {
            abs_assert(
                &UnboundedInterval.abs_bound_pair(),
                &UnboundedInterval.emptiable_abs_bound_pair(),
                &UnboundedInterval.emptiable_abs_bound_pair(),
            );
            assert_eq!(UnboundedInterval.abridge(&UnboundedInterval), UnboundedInterval);
        }
    }

    mod unbounded_empty {
        use super::*;

        #[test]
        fn outside() {
            abs_assert(
                &UnboundedInterval.abs_bound_pair(),
                &EmptiableAbsoluteBoundPair::Empty,
                &UnboundedInterval.emptiable_abs_bound_pair(),
            );
            assert_eq!(UnboundedInterval.abridge(&EmptyInterval), UnboundedInterval);
        }
    }

    mod empty_bounded {
        use super::*;

        #[test]
        fn outside() -> Result<(), Box<dyn Error>> {
            let bounded = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert_empty(
                &EmptiableAbsoluteBoundPair::Empty,
                &bounded.clone().to_emptiable(),
                &bounded.clone().to_emptiable(),
            );
            assert_eq!(
                EmptyInterval.abridge(&BoundedAbsoluteInterval::try_from(bounded.clone())?),
                BoundedAbsoluteInterval::try_from(bounded.clone())?
            );

            Ok(())
        }
    }

    mod empty_half_bounded {
        use super::*;

        #[test]
        fn outside_to_future() -> Result<(), Box<dyn Error>> {
            let half_bounded = AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            );

            abs_assert_empty(
                &EmptiableAbsoluteBoundPair::Empty,
                &half_bounded.clone().to_emptiable(),
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                EmptyInterval.abridge(&HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?),
                HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }

        #[test]
        fn outside_to_past() -> Result<(), Box<dyn Error>> {
            let half_bounded = AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBoundPosition::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            abs_assert_empty(
                &EmptiableAbsoluteBoundPair::Empty,
                &half_bounded.clone().to_emptiable(),
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                EmptyInterval.abridge(&HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?),
                HalfBoundedAbsoluteInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }
    }

    mod empty_unbounded {
        use super::*;

        #[test]
        fn outside() {
            abs_assert_empty(
                &EmptiableAbsoluteBoundPair::Empty,
                &UnboundedInterval.emptiable_abs_bound_pair(),
                &UnboundedInterval.emptiable_abs_bound_pair(),
            );
            assert_eq!(EmptyInterval.abridge(&UnboundedInterval), UnboundedInterval);
        }
    }

    mod empty_empty {
        use super::*;

        #[test]
        fn outside() {
            abs_assert_empty(
                &EmptiableAbsoluteBoundPair::Empty,
                &EmptiableAbsoluteBoundPair::Empty,
                &EmptiableAbsoluteBoundPair::Empty,
            );
            assert_eq!(EmptyInterval.abridge(&EmptyInterval), EmptyInterval);
        }
    }
}

mod relative {
    use super::*;

    mod bounded_bounded {
        use super::*;

        #[test]
        fn outside_before() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_REL
                .get("outside_before")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(3), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn outside_after() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_REL
                .get("outside_after")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(3), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("ends_on_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("ends_on_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("ends_on_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());

                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("ends_on_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("starts_on_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("starts_on_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("starts_on_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("starts_on_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        #[test]
        fn crosses_start() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_REL
                .get("crosses_start")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn crosses_end() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_REL
                .get("crosses_end")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn inside() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_REL.get("inside").cloned().ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod inside_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("inside_and_same_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("inside_and_same_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("inside_and_same_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("inside_and_same_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod inside_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("inside_and_same_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("inside_and_same_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("inside_and_same_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("inside_and_same_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod equal {
            use super::*;

            #[test]
            fn start_inclusive_inclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_incl_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_inclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_incl_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_inclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_incl_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_inclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_incl_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_exclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_excl_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_exclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_excl_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_exclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_excl_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_exclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_excl_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_inclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_incl_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_inclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_incl_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_inclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_incl_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_inclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_incl_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_exclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_excl_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_exclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_excl_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_exclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_excl_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_exclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_excl_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod contains_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("contains_and_same_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("contains_and_same_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("contains_and_same_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("contains_and_same_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod contains_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("contains_and_same_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("contains_and_same_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("contains_and_same_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("contains_and_same_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        #[test]
        fn contains() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_REL.get("contains").cloned().ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }
    }

    mod bounded_half_bounded {
        use super::*;

        #[test]
        fn outside_before() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_HALF_BOUNDED_REL
                .get("outside_before")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(3), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn outside_after() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_HALF_BOUNDED_REL
                .get("outside_after")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("ends_on_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("ends_on_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("ends_on_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("ends_on_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("starts_on_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("starts_on_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("starts_on_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("starts_on_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        #[test]
        fn crosses_start() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_HALF_BOUNDED_REL
                .get("crosses_start")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn crosses_end() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_HALF_BOUNDED_REL
                .get("crosses_end")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod inside {
            use super::*;

            #[test]
            fn to_future() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_to_future")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn to_past() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_to_past")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod inside_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_and_same_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_and_same_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_and_same_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_and_same_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod inside_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_and_same_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_and_same_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_and_same_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_and_same_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    BoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }
    }

    mod bounded_unbounded {
        use super::*;

        #[test]
        fn inside() -> Result<(), Box<dyn Error>> {
            let bounded = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            rel_assert(
                &bounded.clone(),
                &UnboundedInterval.emptiable_rel_bound_pair(),
                &bounded.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelativeInterval::try_from(bounded.clone())?.abridge(&UnboundedInterval),
                BoundedRelativeInterval::try_from(bounded.clone())?
            );

            Ok(())
        }
    }

    mod bounded_empty {
        use super::*;

        #[test]
        fn outside() -> Result<(), Box<dyn Error>> {
            let bounded = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            rel_assert(
                &bounded.clone(),
                &EmptiableRelativeBoundPair::Empty,
                &bounded.clone().to_emptiable(),
            );
            assert_eq!(
                BoundedRelativeInterval::try_from(bounded.clone())?.abridge(&EmptyInterval),
                BoundedRelativeInterval::try_from(bounded.clone())?
            );

            Ok(())
        }
    }

    mod half_bounded_bounded {
        use super::*;

        #[test]
        fn outside_before() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_BOUNDED_REL
                .get("outside_before")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn outside_after() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_BOUNDED_REL
                .get("outside_after")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(3), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("starts_on_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("starts_on_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("starts_on_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("starts_on_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("ends_on_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("ends_on_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("ends_on_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("ends_on_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        #[test]
        fn crosses_start() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_BOUNDED_REL
                .get("crosses_start")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn crosses_end() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_BOUNDED_REL
                .get("crosses_end")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod contains_and_same_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_and_same_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_and_same_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_and_same_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_and_same_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive,
                    )
                    .to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod contains_and_same_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_and_same_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_and_same_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_and_same_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_and_same_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive,
                    )
                    .to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod contains {
            use super::*;

            #[test]
            fn to_future() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_to_future")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn to_past() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_to_past")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&BoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }
    }

    mod half_bounded_half_bounded {
        use super::*;

        #[test]
        fn outside_before() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_REL
                .get("outside_before")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn outside_after() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_REL
                .get("outside_after")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(1), BoundInclusivity::Exclusive)
                    .to_start_bound(),
                RelativeFiniteBoundPosition::new_with_inclusivity(SignedDuration::from_hours(2), BoundInclusivity::Exclusive)
                    .to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod ends_on_start {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_REL
                    .get("ends_on_start_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_REL
                    .get("ends_on_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_REL
                    .get("ends_on_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_REL
                    .get("ends_on_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        mod starts_on_end {
            use super::*;

            #[test]
            fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_REL
                    .get("starts_on_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_REL
                    .get("starts_on_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_REL
                    .get("starts_on_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = EmptiableRelativeBoundPair::Empty;

                rel_assert(&data.0.clone(), &data.1.clone().to_emptiable(), &expected.clone());
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_REL
                    .get("starts_on_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                let expected = RelativeBoundPair::new(
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                );

                rel_assert(
                    &data.0.clone(),
                    &data.1.clone().to_emptiable(),
                    &expected.clone().to_emptiable(),
                );
                assert_eq!(
                    HalfBoundedRelativeInterval::try_from(data.0.clone())?
                        .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                    expected.clone().to_emptiable_interval()
                );

                Ok(())
            }
        }

        #[test]
        fn crosses_start() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_REL
                .get("crosses_start")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn crosses_end() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_REL
                .get("crosses_end")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn inside_and_same_start() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_REL
                .get("inside_and_same_start")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn inside_and_same_end() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_REL
                .get("inside_and_same_end")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelativeEndBound::InfiniteFuture,
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        mod equal {
            use super::*;

            mod to_future {
                use super::*;

                #[test]
                fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_REL
                        .get("equal_to_future_incl_incl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = RelativeBoundPair::new(
                        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeEndBound::InfiniteFuture,
                    );

                    rel_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedRelativeInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }

                #[test]
                fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_REL
                        .get("equal_to_future_incl_excl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = RelativeBoundPair::new(
                        RelativeFiniteBoundPosition::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        RelativeEndBound::InfiniteFuture,
                    );

                    rel_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedRelativeInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }

                #[test]
                fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_REL
                        .get("equal_to_future_excl_incl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = RelativeBoundPair::new(
                        RelativeFiniteBoundPosition::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        RelativeEndBound::InfiniteFuture,
                    );

                    rel_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedRelativeInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }

                #[test]
                fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_REL
                        .get("equal_to_future_excl_excl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = RelativeBoundPair::new(
                        RelativeFiniteBoundPosition::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        RelativeEndBound::InfiniteFuture,
                    );

                    rel_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedRelativeInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }
            }

            mod to_past {
                use super::*;

                #[test]
                fn inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_REL
                        .get("equal_to_past_incl_incl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = RelativeBoundPair::new(
                        RelativeStartBound::InfinitePast,
                        RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
                    );

                    rel_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedRelativeInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }

                #[test]
                fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_REL
                        .get("equal_to_past_incl_excl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = RelativeBoundPair::new(
                        RelativeStartBound::InfinitePast,
                        RelativeFiniteBoundPosition::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    );

                    rel_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedRelativeInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }

                #[test]
                fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_REL
                        .get("equal_to_past_excl_incl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = RelativeBoundPair::new(
                        RelativeStartBound::InfinitePast,
                        RelativeFiniteBoundPosition::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    );

                    rel_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedRelativeInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }

                #[test]
                fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_REL
                        .get("equal_to_past_excl_excl")
                        .cloned()
                        .ok_or("data not found")?;

                    let expected = RelativeBoundPair::new(
                        RelativeStartBound::InfinitePast,
                        RelativeFiniteBoundPosition::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    );

                    rel_assert(
                        &data.0.clone(),
                        &data.1.clone().to_emptiable(),
                        &expected.clone().to_emptiable(),
                    );
                    assert_eq!(
                        HalfBoundedRelativeInterval::try_from(data.0.clone())?
                            .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                        expected.clone().to_emptiable_interval()
                    );

                    Ok(())
                }
            }
        }

        #[test]
        fn contains_and_same_start() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_REL
                .get("contains_and_same_start")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }

        #[test]
        fn contains_and_same_end() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_REL
                .get("contains_and_same_end")
                .cloned()
                .ok_or("data not found")?;

            let expected = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_start_bound(),
                RelativeEndBound::InfiniteFuture,
            );

            rel_assert(
                &data.0.clone(),
                &data.1.clone().to_emptiable(),
                &expected.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(data.0.clone())?
                    .abridge(&HalfBoundedRelativeInterval::try_from(data.1.clone())?),
                expected.clone().to_emptiable_interval()
            );

            Ok(())
        }
    }

    mod half_bounded_unbounded {
        use super::*;

        #[test]
        fn inside_and_same_start() -> Result<(), Box<dyn Error>> {
            let half_bounded = RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
            );

            rel_assert(
                &half_bounded.clone(),
                &UnboundedInterval.emptiable_rel_bound_pair(),
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(half_bounded.clone())?.abridge(&UnboundedInterval),
                HalfBoundedRelativeInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }

        #[test]
        fn inside_and_same_end() -> Result<(), Box<dyn Error>> {
            let half_bounded = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeEndBound::InfiniteFuture,
            );

            rel_assert(
                &half_bounded.clone(),
                &UnboundedInterval.emptiable_rel_bound_pair(),
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(half_bounded.clone())?.abridge(&UnboundedInterval),
                HalfBoundedRelativeInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }
    }

    mod half_bounded_empty {
        use super::*;

        #[test]
        fn outside_to_past() -> Result<(), Box<dyn Error>> {
            let half_bounded = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeEndBound::InfiniteFuture,
            );

            rel_assert(
                &half_bounded.clone(),
                &EmptiableRelativeBoundPair::Empty,
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(half_bounded.clone())?.abridge(&EmptyInterval),
                HalfBoundedRelativeInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }

        #[test]
        fn outside_to_future() -> Result<(), Box<dyn Error>> {
            let half_bounded = RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
            );

            rel_assert(
                &half_bounded.clone(),
                &EmptiableRelativeBoundPair::Empty,
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                HalfBoundedRelativeInterval::try_from(half_bounded.clone())?.abridge(&EmptyInterval),
                HalfBoundedRelativeInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }
    }

    mod unbounded_bounded {
        use super::*;

        #[test]
        fn contains() -> Result<(), Box<dyn Error>> {
            let bounded = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            rel_assert(
                &UnboundedInterval.rel_bound_pair(),
                &bounded.clone().to_emptiable(),
                &bounded.clone().to_emptiable(),
            );
            assert_eq!(
                UnboundedInterval.abridge(&BoundedRelativeInterval::try_from(bounded.clone())?),
                BoundedRelativeInterval::try_from(bounded.clone())?
            );

            Ok(())
        }
    }

    mod unbounded_half_bounded {
        use super::*;

        #[test]
        fn contains_and_same_start() -> Result<(), Box<dyn Error>> {
            let half_bounded = RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
            );

            rel_assert(
                &UnboundedInterval.rel_bound_pair(),
                &half_bounded.clone().to_emptiable(),
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                UnboundedInterval.abridge(&HalfBoundedRelativeInterval::try_from(half_bounded.clone())?),
                HalfBoundedRelativeInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }

        #[test]
        fn contains_and_same_end() -> Result<(), Box<dyn Error>> {
            let half_bounded = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeEndBound::InfiniteFuture,
            );

            rel_assert(
                &UnboundedInterval.rel_bound_pair(),
                &half_bounded.clone().to_emptiable(),
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                UnboundedInterval.abridge(&HalfBoundedRelativeInterval::try_from(half_bounded.clone())?),
                HalfBoundedRelativeInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }
    }

    mod unbounded_unbounded {
        use super::*;

        #[test]
        fn equal() {
            rel_assert(
                &UnboundedInterval.rel_bound_pair(),
                &UnboundedInterval.emptiable_rel_bound_pair(),
                &UnboundedInterval.emptiable_rel_bound_pair(),
            );
        }
    }

    mod unbounded_empty {
        use super::*;

        #[test]
        fn outside() {
            rel_assert(
                &UnboundedInterval.rel_bound_pair(),
                &EmptiableRelativeBoundPair::Empty,
                &UnboundedInterval.emptiable_rel_bound_pair(),
            );
        }
    }

    mod empty_bounded {
        use super::*;

        #[test]
        fn outside() -> Result<(), Box<dyn Error>> {
            let bounded = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            rel_assert_empty(
                &EmptiableRelativeBoundPair::Empty,
                &bounded.clone().to_emptiable(),
                &bounded.clone().to_emptiable(),
            );
            assert_eq!(
                EmptyInterval.abridge(&BoundedRelativeInterval::try_from(bounded.clone())?),
                BoundedRelativeInterval::try_from(bounded.clone())?
            );

            Ok(())
        }
    }

    mod empty_half_bounded {
        use super::*;

        #[test]
        fn outside_to_future() -> Result<(), Box<dyn Error>> {
            let half_bounded = RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeEndBound::InfiniteFuture,
            );

            rel_assert_empty(
                &EmptiableRelativeBoundPair::Empty,
                &half_bounded.clone().to_emptiable(),
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                EmptyInterval.abridge(&HalfBoundedRelativeInterval::try_from(half_bounded.clone())?),
                HalfBoundedRelativeInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }

        #[test]
        fn outside_to_past() -> Result<(), Box<dyn Error>> {
            let half_bounded = RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
            );

            rel_assert_empty(
                &EmptiableRelativeBoundPair::Empty,
                &half_bounded.clone().to_emptiable(),
                &half_bounded.clone().to_emptiable(),
            );
            assert_eq!(
                EmptyInterval.abridge(&HalfBoundedRelativeInterval::try_from(half_bounded.clone())?),
                HalfBoundedRelativeInterval::try_from(half_bounded.clone())?
            );

            Ok(())
        }
    }

    mod empty_unbounded {
        use super::*;

        #[test]
        fn outside() {
            rel_assert_empty(
                &EmptiableRelativeBoundPair::Empty,
                &UnboundedInterval.emptiable_rel_bound_pair(),
                &UnboundedInterval.emptiable_rel_bound_pair(),
            );
        }
    }

    mod empty_empty {
        use super::*;

        #[test]
        fn outside() {
            rel_assert_empty(
                &EmptiableRelativeBoundPair::Empty,
                &EmptiableRelativeBoundPair::Empty,
                &EmptiableRelativeBoundPair::Empty,
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

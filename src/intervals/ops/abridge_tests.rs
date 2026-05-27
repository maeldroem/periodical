use std::error::Error;

use jiff::{SignedDuration, Timestamp};

use super::abridge::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteStartBound,
    EmptiableAbsoluteBoundPair,
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
    EmptiableRelativeBoundPair,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeStartBound,
};

mod abs_bound_pair {
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound()
                )
                .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound()
                )
                .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                )
                .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                )
                .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                )
                .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable(),
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable(),
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable(),
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable(),
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                )
                .to_emptiable(),
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound()
                )
                .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound()
                )
                .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                )
                .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                )
                .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );
            let unbounded = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

            assert_eq!(bounded.abridge(&unbounded.to_emptiable()), bounded.to_emptiable());

            Ok(())
        }
    }

    mod bounded_empty {
        use super::*;

        #[test]
        fn outside() -> Result<(), Box<dyn Error>> {
            let bounded = AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            assert_eq!(
                bounded.abridge(&EmptiableAbsoluteBoundPair::Empty),
                bounded.to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound(),
                )
                .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-03 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound(),
                )
                .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                )
                .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                )
                .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new_with_inclusivity(
                            "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-03 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                    )
                    .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound()
                )
                .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    AbsoluteFiniteBound::new_with_inclusivity(
                        "2026-01-02 00:00:00Z".parse::<Timestamp>()?,
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound()
                )
                .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableAbsoluteBoundPair::Empty
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    AbsoluteBoundPair::new(
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                        AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()
                    )
                    .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                )
                .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                )
                .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                )
                .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                )
                .to_emptiable()
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

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        AbsoluteBoundPair::new(
                            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                            AbsoluteEndBound::InfiniteFuture,
                        )
                        .to_emptiable()
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

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        AbsoluteBoundPair::new(
                            AbsoluteFiniteBound::new_with_inclusivity(
                                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                                BoundInclusivity::Exclusive
                            )
                            .to_start_bound(),
                            AbsoluteEndBound::InfiniteFuture,
                        )
                        .to_emptiable()
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

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        AbsoluteBoundPair::new(
                            AbsoluteFiniteBound::new_with_inclusivity(
                                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                                BoundInclusivity::Exclusive
                            )
                            .to_start_bound(),
                            AbsoluteEndBound::InfiniteFuture,
                        )
                        .to_emptiable()
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

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        AbsoluteBoundPair::new(
                            AbsoluteFiniteBound::new_with_inclusivity(
                                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                                BoundInclusivity::Exclusive
                            )
                            .to_start_bound(),
                            AbsoluteEndBound::InfiniteFuture,
                        )
                        .to_emptiable()
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

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        AbsoluteBoundPair::new(
                            AbsoluteStartBound::InfinitePast,
                            AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                        )
                        .to_emptiable()
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

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        AbsoluteBoundPair::new(
                            AbsoluteStartBound::InfinitePast,
                            AbsoluteFiniteBound::new_with_inclusivity(
                                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                                BoundInclusivity::Exclusive
                            )
                            .to_end_bound(),
                        )
                        .to_emptiable()
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

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        AbsoluteBoundPair::new(
                            AbsoluteStartBound::InfinitePast,
                            AbsoluteFiniteBound::new_with_inclusivity(
                                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                                BoundInclusivity::Exclusive
                            )
                            .to_end_bound(),
                        )
                        .to_emptiable()
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

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        AbsoluteBoundPair::new(
                            AbsoluteStartBound::InfinitePast,
                            AbsoluteFiniteBound::new_with_inclusivity(
                                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                                BoundInclusivity::Exclusive
                            )
                            .to_end_bound(),
                        )
                        .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteStartBound::InfinitePast,
                    AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
                )
                .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                AbsoluteBoundPair::new(
                    AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                    AbsoluteEndBound::InfiniteFuture,
                )
                .to_emptiable()
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
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );
            let unbounded = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

            assert_eq!(
                half_bounded.abridge(&unbounded.to_emptiable()),
                half_bounded.to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn inside_and_same_end() -> Result<(), Box<dyn Error>> {
            let half_bounded = AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            );
            let unbounded = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

            assert_eq!(
                half_bounded.abridge(&unbounded.to_emptiable()),
                half_bounded.to_emptiable()
            );

            Ok(())
        }
    }

    mod half_bounded_empty {
        use super::*;

        #[test]
        fn outside_to_past() -> Result<(), Box<dyn Error>> {
            let half_bounded = AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            );

            assert_eq!(
                half_bounded.abridge(&EmptiableAbsoluteBoundPair::Empty),
                half_bounded.to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn outside_to_future() -> Result<(), Box<dyn Error>> {
            let half_bounded = AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            assert_eq!(
                half_bounded.abridge(&EmptiableAbsoluteBoundPair::Empty),
                half_bounded.to_emptiable()
            );

            Ok(())
        }
    }

    mod unbounded_bounded {
        use super::*;

        #[test]
        fn contains() -> Result<(), Box<dyn Error>> {
            let unbounded = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
            let bounded = AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteFiniteBound::new("2026-01-02 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            assert_eq!(
                unbounded.abridge(&bounded.clone().to_emptiable()),
                bounded.to_emptiable()
            );

            Ok(())
        }
    }

    mod unbounded_half_bounded {
        use super::*;

        #[test]
        fn contains_and_same_start() -> Result<(), Box<dyn Error>> {
            let unbounded = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
            let half_bounded = AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound(),
            );

            assert_eq!(
                unbounded.abridge(&half_bounded.clone().to_emptiable()),
                half_bounded.to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn contains_and_same_end() -> Result<(), Box<dyn Error>> {
            let unbounded = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);
            let half_bounded = AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            );

            assert_eq!(
                unbounded.abridge(&half_bounded.clone().to_emptiable()),
                half_bounded.to_emptiable()
            );

            Ok(())
        }
    }

    mod unbounded_unbounded {
        use super::*;

        #[test]
        fn equal() {
            let unbounded = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

            assert_eq!(
                unbounded.abridge(&unbounded.clone().to_emptiable()),
                unbounded.to_emptiable()
            );
        }
    }

    mod unbounded_empty {
        use super::*;

        #[test]
        fn outside() {
            let unbounded = AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture);

            assert_eq!(
                unbounded.abridge(&EmptiableAbsoluteBoundPair::Empty),
                unbounded.to_emptiable()
            );
        }
    }
}

mod rel_bound_pair {
    use super::*;

    mod bounded_bounded {
        use super::*;

        #[test]
        fn outside_before() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_REL
                .get("outside_before")
                .cloned()
                .ok_or("data not found")?;

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound()
                )
                .to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn outside_after() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_REL
                .get("outside_after")
                .cloned()
                .ok_or("data not found")?;

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound()
                )
                .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("ends_on_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("ends_on_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("ends_on_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("starts_on_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("starts_on_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("starts_on_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
                    )
                    .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound()
                )
                .to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn crosses_end() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_REL
                .get("crosses_end")
                .cloned()
                .ok_or("data not found")?;

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound()
                )
                .to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn inside() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_REL.get("inside").cloned().ok_or("data not found")?;

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound()
                )
                .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("inside_and_same_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("inside_and_same_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("inside_and_same_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("inside_and_same_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(3),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound()
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("inside_and_same_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(3),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound()
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("inside_and_same_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(3),
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_inclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_incl_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_inclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_incl_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_inclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_incl_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_exclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_excl_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_exclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_excl_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_exclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_excl_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_inclusive_exclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_incl_excl_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_inclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_incl_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_inclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_incl_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_inclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_incl_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_inclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_incl_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_exclusive_end_inclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_excl_end_incl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_exclusive_end_inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_excl_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_exclusive_end_exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_excl_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn start_exclusive_exclusive_end_exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("equal_start_excl_excl_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("contains_and_same_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("contains_and_same_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("contains_and_same_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                    )
                    .to_emptiable(),
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("contains_and_same_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(3),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable(),
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("contains_and_same_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(3),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable(),
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_BOUNDED_REL
                    .get("contains_and_same_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(3),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable(),
                );

                Ok(())
            }
        }

        #[test]
        fn contains() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_BOUNDED_REL.get("contains").cloned().ok_or("data not found")?;

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                )
                .to_emptiable(),
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound()
                )
                .to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn outside_after() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_HALF_BOUNDED_REL
                .get("outside_after")
                .cloned()
                .ok_or("data not found")?;

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound()
                )
                .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("ends_on_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("ends_on_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("ends_on_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("starts_on_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("starts_on_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("starts_on_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
                    )
                    .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound()
                )
                .to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn crosses_end() -> Result<(), Box<dyn Error>> {
            let data = BOUNDED_HALF_BOUNDED_REL
                .get("crosses_end")
                .cloned()
                .ok_or("data not found")?;

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
                )
                .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn to_past() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_to_past")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_and_same_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_and_same_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_and_same_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_and_same_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_and_same_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = BOUNDED_HALF_BOUNDED_REL
                    .get("inside_and_same_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }
        }
    }

    mod bounded_unbounded {
        use super::*;

        #[test]
        fn inside() {
            let bounded = RelativeBoundPair::new(
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
            );
            let unbounded = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

            assert_eq!(bounded.abridge(&unbounded.to_emptiable()), bounded.to_emptiable());
        }
    }

    mod bounded_empty {
        use super::*;

        #[test]
        fn outside() {
            let bounded = RelativeBoundPair::new(
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            assert_eq!(
                bounded.abridge(&EmptiableRelativeBoundPair::Empty),
                bounded.to_emptiable()
            );
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound(),
                )
                .to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn outside_after() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_BOUNDED_REL
                .get("outside_after")
                .cloned()
                .ok_or("data not found")?;

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(3),
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound(),
                )
                .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("starts_on_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("starts_on_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("starts_on_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("ends_on_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("ends_on_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("ends_on_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
                    )
                    .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                )
                .to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn crosses_end() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_BOUNDED_REL
                .get("crosses_end")
                .cloned()
                .ok_or("data not found")?;

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                )
                .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_and_same_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_and_same_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_and_same_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(1),
                            BoundInclusivity::Exclusive,
                        )
                        .to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_and_same_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_and_same_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_and_same_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new_with_inclusivity(
                            SignedDuration::from_hours(2),
                            BoundInclusivity::Exclusive,
                        )
                        .to_end_bound(),
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(3)).to_end_bound(),
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn to_past() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_BOUNDED_REL
                    .get("contains_to_past")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                    )
                    .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound()
                )
                .to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn outside_after() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_REL
                .get("outside_after")
                .cloned()
                .ok_or("data not found")?;

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(1),
                        BoundInclusivity::Exclusive
                    )
                    .to_start_bound(),
                    RelativeFiniteBound::new_with_inclusivity(
                        SignedDuration::from_hours(2),
                        BoundInclusivity::Exclusive
                    )
                    .to_end_bound()
                )
                .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_REL
                    .get("ends_on_start_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_REL
                    .get("ends_on_start_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_REL
                    .get("ends_on_start_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
                    )
                    .to_emptiable()
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

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
                    )
                    .to_emptiable()
                );

                Ok(())
            }

            #[test]
            fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_REL
                    .get("starts_on_end_incl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_REL
                    .get("starts_on_end_excl_incl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    EmptiableRelativeBoundPair::Empty
                );

                Ok(())
            }

            #[test]
            fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                let data = HALF_BOUNDED_HALF_BOUNDED_REL
                    .get("starts_on_end_excl_excl")
                    .cloned()
                    .ok_or("data not found")?;

                assert_eq!(
                    data.0.abridge(&data.1.to_emptiable()),
                    RelativeBoundPair::new(
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                        RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound()
                    )
                    .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                )
                .to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn crosses_end() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_REL
                .get("crosses_end")
                .cloned()
                .ok_or("data not found")?;

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
                )
                .to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn inside_and_same_start() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_REL
                .get("inside_and_same_start")
                .cloned()
                .ok_or("data not found")?;

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
                )
                .to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn inside_and_same_end() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_REL
                .get("inside_and_same_end")
                .cloned()
                .ok_or("data not found")?;

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                )
                .to_emptiable()
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

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        RelativeBoundPair::new(
                            RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                            RelativeEndBound::InfiniteFuture,
                        )
                        .to_emptiable()
                    );

                    Ok(())
                }

                #[test]
                fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_REL
                        .get("equal_to_future_incl_excl")
                        .cloned()
                        .ok_or("data not found")?;

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        RelativeBoundPair::new(
                            RelativeFiniteBound::new_with_inclusivity(
                                SignedDuration::from_hours(1),
                                BoundInclusivity::Exclusive
                            )
                            .to_start_bound(),
                            RelativeEndBound::InfiniteFuture,
                        )
                        .to_emptiable()
                    );

                    Ok(())
                }

                #[test]
                fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_REL
                        .get("equal_to_future_excl_incl")
                        .cloned()
                        .ok_or("data not found")?;

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        RelativeBoundPair::new(
                            RelativeFiniteBound::new_with_inclusivity(
                                SignedDuration::from_hours(1),
                                BoundInclusivity::Exclusive
                            )
                            .to_start_bound(),
                            RelativeEndBound::InfiniteFuture,
                        )
                        .to_emptiable()
                    );

                    Ok(())
                }

                #[test]
                fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_REL
                        .get("equal_to_future_excl_excl")
                        .cloned()
                        .ok_or("data not found")?;

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        RelativeBoundPair::new(
                            RelativeFiniteBound::new_with_inclusivity(
                                SignedDuration::from_hours(1),
                                BoundInclusivity::Exclusive
                            )
                            .to_start_bound(),
                            RelativeEndBound::InfiniteFuture,
                        )
                        .to_emptiable()
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

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        RelativeBoundPair::new(
                            RelativeStartBound::InfinitePast,
                            RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
                        )
                        .to_emptiable()
                    );

                    Ok(())
                }

                #[test]
                fn inclusive_exclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_REL
                        .get("equal_to_past_incl_excl")
                        .cloned()
                        .ok_or("data not found")?;

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        RelativeBoundPair::new(
                            RelativeStartBound::InfinitePast,
                            RelativeFiniteBound::new_with_inclusivity(
                                SignedDuration::from_hours(1),
                                BoundInclusivity::Exclusive
                            )
                            .to_end_bound(),
                        )
                        .to_emptiable()
                    );

                    Ok(())
                }

                #[test]
                fn exclusive_inclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_REL
                        .get("equal_to_past_excl_incl")
                        .cloned()
                        .ok_or("data not found")?;

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        RelativeBoundPair::new(
                            RelativeStartBound::InfinitePast,
                            RelativeFiniteBound::new_with_inclusivity(
                                SignedDuration::from_hours(1),
                                BoundInclusivity::Exclusive
                            )
                            .to_end_bound(),
                        )
                        .to_emptiable()
                    );

                    Ok(())
                }

                #[test]
                fn exclusive_exclusive() -> Result<(), Box<dyn Error>> {
                    let data = HALF_BOUNDED_HALF_BOUNDED_REL
                        .get("equal_to_past_excl_excl")
                        .cloned()
                        .ok_or("data not found")?;

                    assert_eq!(
                        data.0.abridge(&data.1.to_emptiable()),
                        RelativeBoundPair::new(
                            RelativeStartBound::InfinitePast,
                            RelativeFiniteBound::new_with_inclusivity(
                                SignedDuration::from_hours(1),
                                BoundInclusivity::Exclusive
                            )
                            .to_end_bound(),
                        )
                        .to_emptiable()
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

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeStartBound::InfinitePast,
                    RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
                )
                .to_emptiable()
            );

            Ok(())
        }

        #[test]
        fn contains_and_same_end() -> Result<(), Box<dyn Error>> {
            let data = HALF_BOUNDED_HALF_BOUNDED_REL
                .get("contains_and_same_end")
                .cloned()
                .ok_or("data not found")?;

            assert_eq!(
                data.0.abridge(&data.1.to_emptiable()),
                RelativeBoundPair::new(
                    RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_start_bound(),
                    RelativeEndBound::InfiniteFuture,
                )
                .to_emptiable()
            );

            Ok(())
        }
    }

    mod half_bounded_unbounded {
        use super::*;

        #[test]
        fn inside_and_same_start() {
            let half_bounded = RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
            );
            let unbounded = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

            assert_eq!(
                half_bounded.abridge(&unbounded.to_emptiable()),
                half_bounded.to_emptiable()
            );
        }

        #[test]
        fn inside_and_same_end() {
            let half_bounded = RelativeBoundPair::new(
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeEndBound::InfiniteFuture,
            );
            let unbounded = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

            assert_eq!(
                half_bounded.abridge(&unbounded.to_emptiable()),
                half_bounded.to_emptiable()
            );
        }
    }

    mod half_bounded_empty {
        use super::*;

        #[test]
        fn outside_to_past() {
            let half_bounded = RelativeBoundPair::new(
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeEndBound::InfiniteFuture,
            );

            assert_eq!(
                half_bounded.abridge(&EmptiableRelativeBoundPair::Empty),
                half_bounded.to_emptiable()
            );
        }

        #[test]
        fn outside_to_future() {
            let half_bounded = RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
            );

            assert_eq!(
                half_bounded.abridge(&EmptiableRelativeBoundPair::Empty),
                half_bounded.to_emptiable()
            );
        }
    }

    mod unbounded_bounded {
        use super::*;

        #[test]
        fn contains() {
            let unbounded = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
            let bounded = RelativeBoundPair::new(
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeFiniteBound::new(SignedDuration::from_hours(2)).to_end_bound(),
            );

            assert_eq!(
                unbounded.abridge(&bounded.clone().to_emptiable()),
                bounded.to_emptiable()
            );
        }
    }

    mod unbounded_half_bounded {
        use super::*;

        #[test]
        fn contains_and_same_start() {
            let unbounded = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
            let half_bounded = RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_end_bound(),
            );

            assert_eq!(
                unbounded.abridge(&half_bounded.clone().to_emptiable()),
                half_bounded.to_emptiable()
            );
        }

        #[test]
        fn contains_and_same_end() {
            let unbounded = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);
            let half_bounded = RelativeBoundPair::new(
                RelativeFiniteBound::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeEndBound::InfiniteFuture,
            );

            assert_eq!(
                unbounded.abridge(&half_bounded.clone().to_emptiable()),
                half_bounded.to_emptiable()
            );
        }
    }

    mod unbounded_unbounded {
        use super::*;

        #[test]
        fn equal() {
            let unbounded = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

            assert_eq!(
                unbounded.abridge(&unbounded.clone().to_emptiable()),
                unbounded.to_emptiable()
            );
        }
    }

    mod unbounded_empty {
        use super::*;

        #[test]
        fn outside() {
            let unbounded = RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture);

            assert_eq!(
                unbounded.abridge(&EmptiableRelativeBoundPair::Empty),
                unbounded.to_emptiable()
            );
        }
    }
}

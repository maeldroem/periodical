use std::error::Error;

use jiff::Timestamp;

use super::emptiable_interval::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteInterval,
    BoundedAbsoluteInterval,
    EmptiableAbsoluteBoundPair,
    HalfBoundedAbsoluteInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::special::{EmptyInterval, UnboundedInterval};

#[test]
fn from_absolute_bounds() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        EmptiableAbsoluteInterval::from(AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        )),
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::HalfBounded(
            HalfBoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture,
            )
        )),
    );

    Ok(())
}

#[test]
fn from_emptiable_absolute_bounds() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        EmptiableAbsoluteInterval::from(EmptiableAbsoluteBoundPair::Bound(AbsoluteBoundPair::new(
            AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound(),
            AbsoluteEndBound::InfiniteFuture,
        ))),
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::HalfBounded(
            HalfBoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
                OpeningDirection::ToFuture,
            )
        )),
    );

    Ok(())
}

#[test]
fn from_opt_datetime_pair_unbounded() {
    assert_eq!(
        <EmptiableAbsoluteInterval as From<(Option<Timestamp>, Option<Timestamp>)>>::from((None, None)),
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::Unbounded(UnboundedInterval)),
    );
}

#[test]
fn from_opt_datetime_pair_half_bounded() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        EmptiableAbsoluteInterval::from((None, Some("2025-01-01 00:00:00Z".parse::<Timestamp>()?))),
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::HalfBounded(HalfBoundedAbsoluteInterval::new(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            OpeningDirection::ToPast,
        ))),
    );

    Ok(())
}

#[test]
fn from_opt_datetime_bound_inclusivity_pairs() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        EmptiableAbsoluteInterval::from((
            Some((
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )),
            Some((
                "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )),
        )),
        EmptiableAbsoluteInterval::Bound(AbsoluteInterval::Bounded(
            BoundedAbsoluteInterval::new_with_inclusivity(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
                "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
        )),
    );

    Ok(())
}

// #[test]
// fn from_bool_and_two_opt_datetime_empty() {
//     assert_eq!(
//         <EmptiableAbsoluteInterval as From<(bool, Option<Timestamp>, Option<Timestamp>)>>::from((true, None, None,)),
//         EmptiableAbsoluteInterval::Empty(EmptyInterval),
//     );
// }

// #[test]
// fn from_bool_and_two_opt_datetime() -> Result<(), Box<dyn Error>> {
//     assert_eq!(
//         EmptiableAbsoluteInterval::from((
//             false,
//             Some("2025-01-01 00:00:00Z".parse::<Timestamp>()?),
//             Some("2025-01-02 00:00:00Z".parse::<Timestamp>()?),
//         )),
//         EmptiableAbsoluteInterval::Bound(AbsoluteInterval::Bounded(BoundedAbsoluteInterval::new(
//             "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
//             "2025-01-02 00:00:00Z".parse::<Timestamp>()?
//         ))),
//     );

//     Ok(())
// }

// #[test]
// fn from_bool_and_two_opt_datetime_bound_inclusivity_empty() {
//     assert_eq!(
//         <EmptiableAbsoluteInterval as From<(
//             bool,
//             Option<(Timestamp, BoundInclusivity)>,
//             Option<(Timestamp, BoundInclusivity)>
//         )>>::from((true, None, None,)),
//         EmptiableAbsoluteInterval::Empty(EmptyInterval),
//     );
// }

// #[test]
// fn from_bool_and_two_opt_datetime_bound_inclusivity() -> Result<(), Box<dyn Error>> {
//     assert_eq!(
//         EmptiableAbsoluteInterval::from((
//             false,
//             Some((
//                 "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
//                 BoundInclusivity::Exclusive
//             )),
//             Some((
//                 "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
//                 BoundInclusivity::Exclusive
//             )),
//         )),
//         EmptiableAbsoluteInterval::Bound(AbsoluteInterval::Bounded(
//             BoundedAbsoluteInterval::new_with_inclusivity(
//                 "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
//                 BoundInclusivity::Exclusive,
//                 "2025-01-02 00:00:00Z".parse::<Timestamp>()?,
//                 BoundInclusivity::Exclusive,
//             )
//         )),
//     );

//     Ok(())
// }

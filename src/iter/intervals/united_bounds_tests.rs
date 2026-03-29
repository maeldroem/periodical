use std::error::Error;

use jiff::{SignedDuration, Zoned};

use super::united_bounds::*;
use crate::intervals::absolute::{
    AbsoluteBound,
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteStartBound,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::relative::{
    RelativeBound,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeStartBound,
};
use crate::iter::intervals::bounds::{AbsoluteBoundsIteratorDispatcher, RelativeBoundsIteratorDispatcher};

mod abs_united_bounds {
    use super::*;

    #[test]
    fn create() -> Result<(), Box<dyn Error>> {
        let data = [
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::InfiniteFuture,
            ),
        ];

        let _ = AbsoluteUnitedBoundsIter::new(data.abs_bounds_iter());

        Ok(())
    }

    #[test]
    fn run() -> Result<(), Box<dyn Error>> {
        let mut data = [
            AbsoluteBound::Start(AbsoluteStartBound::InfinitePast),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-11 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-13 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-17 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-19 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            ))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-02-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture),
            AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                "2025-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
            AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                "2025-06-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
            ))),
        ];

        data.sort();

        assert_eq!(
            AbsoluteUnitedBoundsIter::new(data.into_iter()).collect::<Vec<_>>(),
            vec![
                AbsoluteBound::Start(AbsoluteStartBound::InfinitePast),
                AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture),
            ],
        );

        Ok(())
    }

    #[test]
    fn run_from_abs_bounds_iter() -> Result<(), Box<dyn Error>> {
        let data = [
            AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-11 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-13 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-17 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-19 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new_with_inclusivity(
                    "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::InfiniteFuture,
            ),
            AbsoluteBoundPair::new(
                AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
                AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-06-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                )),
            ),
        ];

        assert_eq!(
            data.abs_bounds_iter().unite_bounds().collect::<Vec<_>>(),
            vec![
                AbsoluteBound::Start(AbsoluteStartBound::InfinitePast),
                AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                AbsoluteBound::End(AbsoluteEndBound::Finite(AbsoluteFiniteBound::new(
                    "2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                AbsoluteBound::Start(AbsoluteStartBound::Finite(AbsoluteFiniteBound::new(
                    "2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp()
                ))),
                AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture),
            ],
        );

        Ok(())
    }
}

mod rel_united_bounds {
    use super::*;

    #[test]
    fn create() {
        let data = [
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(11))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(12))),
            ),
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(16))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(19))),
            ),
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
                RelativeEndBound::InfiniteFuture,
            ),
        ];

        let _ = RelativeUnitedBoundsIter::new(data.rel_bounds_iter());
    }

    #[test]
    fn run() {
        let mut data = [
            RelativeBound::Start(RelativeStartBound::InfinitePast),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(1),
            ))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(12),
            ))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(15),
            ))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(20),
            ))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(30),
            ))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(20),
            ))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(22),
            ))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(21),
            ))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(25),
            ))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(23),
            ))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(27),
            ))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(29),
            ))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(35),
            ))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                SignedDuration::from_hours(35),
                BoundInclusivity::Exclusive,
            ))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(40),
            ))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(50),
            ))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(55),
            ))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(54),
            ))),
            RelativeBound::End(RelativeEndBound::InfiniteFuture),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(101),
            ))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(201),
            ))),
        ];

        data.sort();

        assert_eq!(
            RelativeUnitedBoundsIter::new(data.into_iter()).collect::<Vec<_>>(),
            vec![
                RelativeBound::Start(RelativeStartBound::InfinitePast),
                RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(1)
                ))),
                RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(12)
                ))),
                RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(15)
                ))),
                RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(20)
                ))),
                RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(40)
                ))),
                RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(50)
                ))),
                RelativeBound::End(RelativeEndBound::InfiniteFuture),
            ],
        );
    }

    #[test]
    fn run_from_rel_bounds_iter() {
        let data = [
            RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
            ),
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(12))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(15))),
            ),
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(20))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(30))),
            ),
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(20))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(22))),
            ),
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(21))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(25))),
            ),
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(23))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(27))),
            ),
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(29))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(35))),
            ),
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new_with_inclusivity(
                    SignedDuration::from_hours(35),
                    BoundInclusivity::Exclusive,
                )),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(40))),
            ),
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(50))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(55))),
            ),
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(54))),
                RelativeEndBound::InfiniteFuture,
            ),
            RelativeBoundPair::new(
                RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(101))),
                RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(201))),
            ),
        ];

        assert_eq!(
            data.rel_bounds_iter().unite_bounds().collect::<Vec<_>>(),
            vec![
                RelativeBound::Start(RelativeStartBound::InfinitePast),
                RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(1)
                ))),
                RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(12)
                ))),
                RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(15)
                ))),
                RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(20)
                ))),
                RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(40)
                ))),
                RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                    SignedDuration::from_hours(50)
                ))),
                RelativeBound::End(RelativeEndBound::InfiniteFuture),
            ],
        );
    }
}

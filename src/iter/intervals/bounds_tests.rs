use std::error::Error;

use jiff::{SignedDuration, Zoned};

use super::bounds::*;
use crate::intervals::absolute::{
    AbsoluteBound,
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBound,
    AbsoluteStartBound,
};
use crate::intervals::relative::{
    RelativeBound,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBound,
    RelativeStartBound,
};

mod abs_bounds {
    use super::*;

    #[test]
    fn create_abs_bounds_iter() -> Result<(), Box<dyn Error>> {
        let data = [
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBound::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
        ];

        let _ = AbsoluteBoundsIter::new(data.into_iter());

        Ok(())
    }

    #[test]
    fn abs_bounds_iter_run() -> Result<(), Box<dyn Error>> {
        let data = [
            AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBound::new("2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBound::new("2025-01-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBound::new("2025-01-09 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBound::new("2025-02-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBound::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBound::new("2025-02-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            ),
        ];

        assert_eq!(
            AbsoluteBoundsIter::new(data.into_iter()).collect::<Vec<_>>(),
            vec![
                AbsoluteBound::Start(AbsoluteStartBound::InfinitePast),
                AbsoluteBound::End(
                    AbsoluteFiniteBound::new("2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                AbsoluteBound::Start(
                    AbsoluteFiniteBound::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
                AbsoluteBound::End(
                    AbsoluteFiniteBound::new("2025-01-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                AbsoluteBound::Start(
                    AbsoluteFiniteBound::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
                AbsoluteBound::End(
                    AbsoluteFiniteBound::new("2025-01-09 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                AbsoluteBound::Start(
                    AbsoluteFiniteBound::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
                AbsoluteBound::End(
                    AbsoluteFiniteBound::new("2025-02-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                AbsoluteBound::Start(
                    AbsoluteFiniteBound::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
                AbsoluteBound::End(
                    AbsoluteFiniteBound::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_end_bound()
                ),
                AbsoluteBound::Start(
                    AbsoluteFiniteBound::new("2025-02-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                        .to_start_bound()
                ),
                AbsoluteBound::End(AbsoluteEndBound::InfiniteFuture),
            ],
        );

        Ok(())
    }
}

#[test]
fn create_rel_bounds_iter() {
    let data = [
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
        ),
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(3))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(5))),
        ),
    ];

    let _ = RelativeBoundsIter::new(data.into_iter());
}

#[test]
fn rel_bounds_iter_run() {
    let data = [
        RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(1))),
        ),
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(10))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(15))),
        ),
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(13))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(19))),
        ),
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(20))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(24))),
        ),
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(25))),
            RelativeEndBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(29))),
        ),
        RelativeBoundPair::new(
            RelativeStartBound::Finite(RelativeFiniteBound::new(SignedDuration::from_hours(27))),
            RelativeEndBound::InfiniteFuture,
        ),
    ];

    assert_eq!(
        RelativeBoundsIter::new(data.into_iter()).collect::<Vec<_>>(),
        vec![
            RelativeBound::Start(RelativeStartBound::InfinitePast),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(1)
            ))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(10)
            ))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(15)
            ))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(13)
            ))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(19)
            ))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(20)
            ))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(24)
            ))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(25)
            ))),
            RelativeBound::End(RelativeEndBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(29)
            ))),
            RelativeBound::Start(RelativeStartBound::Finite(RelativeFiniteBound::new(
                SignedDuration::from_hours(27)
            ))),
            RelativeBound::End(RelativeEndBound::InfiniteFuture),
        ],
    );
}

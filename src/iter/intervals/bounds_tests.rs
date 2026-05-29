use std::error::Error;

use jiff::{SignedDuration, Zoned};

use super::bounds::*;
use crate::intervals::absolute::{AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBoundPosition, AbsoluteStartBound};
use crate::intervals::relative::{RelativeBoundPair, RelativeEndBound, RelativeFiniteBoundPosition, RelativeStartBound};

mod abs_bounds {
    use super::*;

    #[test]
    fn create_abs_bounds_iter() -> Result<(), Box<dyn Error>> {
        let data = [
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
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
                AbsoluteFiniteBoundPosition::new("2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-09 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-02-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-02-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            ),
        ];

        assert_eq!(
            AbsoluteBoundsIter::new(data.into_iter()).collect::<Vec<_>>(),
            vec![
                AbsoluteStartBound::InfinitePast.to_bound(),
                AbsoluteFiniteBoundPosition::new("2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-09 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-02-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-02-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsoluteEndBound::InfiniteFuture.to_bound(),
            ],
        );

        Ok(())
    }
}

#[test]
fn create_rel_bounds_iter() {
    let data = [
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        ),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(3)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(5)).to_end_bound(),
        ),
    ];

    let _ = RelativeBoundsIter::new(data.into_iter());
}

#[test]
fn rel_bounds_iter_run() {
    let data = [
        RelativeBoundPair::new(
            RelativeStartBound::InfinitePast,
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
        ),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(10)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(15)).to_end_bound(),
        ),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(13)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(19)).to_end_bound(),
        ),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(20)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(24)).to_end_bound(),
        ),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(25)).to_start_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(29)).to_end_bound(),
        ),
        RelativeBoundPair::new(
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(27)).to_start_bound(),
            RelativeEndBound::InfiniteFuture,
        ),
    ];

    assert_eq!(
        RelativeBoundsIter::new(data.into_iter()).collect::<Vec<_>>(),
        vec![
            RelativeStartBound::InfinitePast.to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
                .to_end_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(10))
                .to_start_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(15))
                .to_end_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(13))
                .to_start_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(19))
                .to_end_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(20))
                .to_start_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(24))
                .to_end_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(25))
                .to_start_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(29))
                .to_end_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(27))
                .to_start_bound()
                .to_bound(),
            RelativeEndBound::InfiniteFuture.to_bound(),
        ],
    );
}

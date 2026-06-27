use std::error::Error;

use jiff::{SignedDuration, Zoned};

use super::bounds::*;
use crate::intervals::absolute::{AbsBoundPair, AbsEndBound, AbsFiniteBoundPos, AbsStartBound};
use crate::intervals::relative::{
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelStartBound,
};

mod abs_bounds {
    use super::*;

    #[test]
    fn create_abs_bounds_iter() -> Result<(), Box<dyn Error>> {
        let data = [
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
        ];

        let _ = AbsBoundsIter::new(data.into_iter());

        Ok(())
    }

    #[test]
    fn abs_bounds_iter_run() -> Result<(), Box<dyn Error>> {
        let data = [
            AbsBoundPair::new(
                AbsStartBound::InfinitePast,
                AbsFiniteBoundPos::new("2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-01-09 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-02-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsFiniteBoundPos::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsBoundPair::new(
                AbsFiniteBoundPos::new("2025-02-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsEndBound::InfiniteFuture,
            ),
        ];

        assert_eq!(
            AbsBoundsIter::new(data.into_iter()).collect::<Vec<_>>(),
            vec![
                AbsStartBound::InfinitePast.to_bound(),
                AbsFiniteBoundPos::new("2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsFiniteBoundPos::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsFiniteBoundPos::new("2025-01-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsFiniteBoundPos::new("2025-01-03 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsFiniteBoundPos::new("2025-01-09 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsFiniteBoundPos::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsFiniteBoundPos::new("2025-02-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsFiniteBoundPos::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsFiniteBoundPos::new("2025-02-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsFiniteBoundPos::new("2025-02-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsEndBound::InfiniteFuture.to_bound(),
            ],
        );

        Ok(())
    }
}

#[test]
fn create_rel_bounds_iter() {
    let data = [
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        ),
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(3)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(5)).to_end_bound(),
        ),
    ];

    let _ = RelBoundsIter::new(data.into_iter());
}

#[test]
fn rel_bounds_iter_run() {
    let data = [
        RelBoundPair::new(
            RelStartBound::InfinitePast,
            RelFiniteBoundPos::new(SignedDuration::from_hours(1)).to_end_bound(),
        ),
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(10)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(15)).to_end_bound(),
        ),
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(13)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(19)).to_end_bound(),
        ),
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(20)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(24)).to_end_bound(),
        ),
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(25)).to_start_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(29)).to_end_bound(),
        ),
        RelBoundPair::new(
            RelFiniteBoundPos::new(SignedDuration::from_hours(27)).to_start_bound(),
            RelEndBound::InfiniteFuture,
        ),
    ];

    assert_eq!(
        RelBoundsIter::new(data.into_iter()).collect::<Vec<_>>(),
        vec![
            RelStartBound::InfinitePast.to_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(1))
                .to_end_bound()
                .to_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(10))
                .to_start_bound()
                .to_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(15))
                .to_end_bound()
                .to_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(13))
                .to_start_bound()
                .to_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(19))
                .to_end_bound()
                .to_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(20))
                .to_start_bound()
                .to_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(24))
                .to_end_bound()
                .to_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(25))
                .to_start_bound()
                .to_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(29))
                .to_end_bound()
                .to_bound(),
            RelFiniteBoundPos::new(SignedDuration::from_hours(27))
                .to_start_bound()
                .to_bound(),
            RelEndBound::InfiniteFuture.to_bound(),
        ],
    );
}

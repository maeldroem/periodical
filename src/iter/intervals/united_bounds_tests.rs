use std::error::Error;

use jiff::{SignedDuration, Zoned};

use super::united_bounds::*;
use crate::intervals::absolute::{
    AbsoluteBoundPair,
    AbsoluteEndBound,
    AbsoluteFiniteBoundPosition,
    AbsoluteStartBound,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::{BoundOrd, BoundOverlapDisambiguationRuleSet};
use crate::intervals::relative::{
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBoundPosition,
    RelativeStartBound,
};
use crate::iter::intervals::bounds::{AbsoluteBoundsIteratorDispatcher, RelativeBoundsIteratorDispatcher};

mod abs_united_bounds {
    use super::*;

    #[test]
    fn create() -> Result<(), Box<dyn Error>> {
        let data = [
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-06 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            ),
        ];

        let _ = AbsoluteUnitedBoundsIter::new(data.abs_bounds_iter());

        Ok(())
    }

    #[test]
    fn run() -> Result<(), Box<dyn Error>> {
        let mut data = [
            AbsoluteStartBound::InfinitePast.to_bound(),
            AbsoluteFiniteBoundPosition::new("2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-11 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-13 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-17 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-19 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new_with_inclusivity(
                "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
            .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-02-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
                .to_bound(),
            AbsoluteEndBound::InfiniteFuture.to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_start_bound()
                .to_bound(),
            AbsoluteFiniteBoundPosition::new("2025-06-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                .to_end_bound()
                .to_bound(),
        ];

        data.sort_by(|a, b| a.bound_cmp(b).disambiguate(BoundOverlapDisambiguationRuleSet::Strict));

        assert_eq!(
            AbsoluteUnitedBoundsIter::new(data.into_iter()).collect::<Vec<_>>(),
            vec![
                AbsoluteStartBound::InfinitePast.to_bound(),
                AbsoluteFiniteBoundPosition::new("2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsoluteEndBound::InfiniteFuture.to_bound(),
            ],
        );

        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    #[test]
    fn run_from_abs_bounds_iter() -> Result<(), Box<dyn Error>> {
        let data = [
            AbsoluteBoundPair::new(
                AbsoluteStartBound::InfinitePast,
                AbsoluteFiniteBoundPosition::new("2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-20 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-12 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-11 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-15 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-13 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-17 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-01-19 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new_with_inclusivity(
                    "2025-01-25 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-02-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-02-04 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteEndBound::InfiniteFuture,
            ),
            AbsoluteBoundPair::new(
                AbsoluteFiniteBoundPosition::new("2025-05-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound(),
                AbsoluteFiniteBoundPosition::new("2025-06-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound(),
            ),
        ];

        assert_eq!(
            data.abs_bounds_iter().unite_bounds().collect::<Vec<_>>(),
            vec![
                AbsoluteStartBound::InfinitePast.to_bound(),
                AbsoluteFiniteBoundPosition::new("2024-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-05 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-10 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-01-30 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_end_bound()
                    .to_bound(),
                AbsoluteFiniteBoundPosition::new("2025-02-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp())
                    .to_start_bound()
                    .to_bound(),
                AbsoluteEndBound::InfiniteFuture.to_bound(),
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
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(11)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(12)).to_end_bound(),
            ),
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(16)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(19)).to_end_bound(),
            ),
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_start_bound(),
                RelativeEndBound::InfiniteFuture,
            ),
        ];

        let _ = RelativeUnitedBoundsIter::new(data.rel_bounds_iter());
    }

    #[test]
    fn run() {
        let mut data = [
            RelativeStartBound::InfinitePast.to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
                .to_end_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(12))
                .to_start_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(15))
                .to_end_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(20))
                .to_start_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(30))
                .to_end_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(20))
                .to_start_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(22))
                .to_end_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(21))
                .to_start_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(25))
                .to_end_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(23))
                .to_start_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(27))
                .to_end_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(29))
                .to_start_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(35))
                .to_end_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new_with_inclusivity(
                SignedDuration::from_hours(35),
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
            .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(40))
                .to_end_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(50))
                .to_start_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(55))
                .to_end_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(54))
                .to_start_bound()
                .to_bound(),
            RelativeEndBound::InfiniteFuture.to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(101))
                .to_start_bound()
                .to_bound(),
            RelativeFiniteBoundPosition::new(SignedDuration::from_hours(201))
                .to_end_bound()
                .to_bound(),
        ];

        data.sort_by(|a, b| a.bound_cmp(b).disambiguate(BoundOverlapDisambiguationRuleSet::Strict));

        assert_eq!(
            RelativeUnitedBoundsIter::new(data.into_iter()).collect::<Vec<_>>(),
            vec![
                RelativeStartBound::InfinitePast.to_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
                    .to_end_bound()
                    .to_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(12))
                    .to_start_bound()
                    .to_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(15))
                    .to_end_bound()
                    .to_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(20))
                    .to_start_bound()
                    .to_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(40))
                    .to_end_bound()
                    .to_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(50))
                    .to_start_bound()
                    .to_bound(),
                RelativeEndBound::InfiniteFuture.to_bound(),
            ],
        );
    }

    #[test]
    fn run_from_rel_bounds_iter() {
        let data = [
            RelativeBoundPair::new(
                RelativeStartBound::InfinitePast,
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1)).to_end_bound(),
            ),
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(12)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(15)).to_end_bound(),
            ),
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(20)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(30)).to_end_bound(),
            ),
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(20)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(22)).to_end_bound(),
            ),
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(21)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(25)).to_end_bound(),
            ),
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(23)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(27)).to_end_bound(),
            ),
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(29)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(35)).to_end_bound(),
            ),
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new_with_inclusivity(
                    SignedDuration::from_hours(35),
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(40)).to_end_bound(),
            ),
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(50)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(55)).to_end_bound(),
            ),
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(54)).to_start_bound(),
                RelativeEndBound::InfiniteFuture,
            ),
            RelativeBoundPair::new(
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(101)).to_start_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(201)).to_end_bound(),
            ),
        ];

        assert_eq!(
            data.rel_bounds_iter().unite_bounds().collect::<Vec<_>>(),
            vec![
                RelativeStartBound::InfinitePast.to_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(1))
                    .to_end_bound()
                    .to_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(12))
                    .to_start_bound()
                    .to_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(15))
                    .to_end_bound()
                    .to_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(20))
                    .to_start_bound()
                    .to_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(40))
                    .to_end_bound()
                    .to_bound(),
                RelativeFiniteBoundPosition::new(SignedDuration::from_hours(50))
                    .to_start_bound()
                    .to_bound(),
                RelativeEndBound::InfiniteFuture.to_bound(),
            ],
        );
    }
}

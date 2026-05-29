//! Interval splitting iterators
//!
//! See [`intervals::ops::split`](crate::intervals::ops::split) for more details.

use jiff::tz::TimeZone;

use crate::intervals::absolute::{
    AbsoluteBoundPair, AbsoluteFiniteBoundPosition, AbsoluteStartBound, BoundedAbsoluteInterval, HalfBoundedAbsoluteInterval,
    HasAbsoluteBoundPair,
};
use crate::intervals::meta::BoundInclusivity;
use crate::intervals::ops::cut::{CutResult, CutType, Cuttable};
use crate::intervals::relative::BoundedRelativeInterval;
use crate::time::CalendarAnchorOffset;

/// Split by [`NaiveDuration`] iterator
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NaiveDurationSplit {
    remaining_interval: AbsoluteBoundPair,
    calendar_anchor_offset: CalendarAnchorOffset,
    tz: TimeZone,
    exhausted: bool,
}

impl NaiveDurationSplit {
    #[must_use]
    pub fn new<I>(interval: &I, calendar_anchor_offset: CalendarAnchorOffset, tz: TimeZone) -> Self
    where
        I: HasAbsoluteBoundPair,
    {
        NaiveDurationSplit {
            remaining_interval: interval.abs_bound_pair(),
            calendar_anchor_offset,
            tz,
            exhausted: false,
        }
    }
}

impl Iterator for NaiveDurationSplit {
    type Item = AbsoluteBoundPair;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        todo!()

        // match self.remaining_interval.start().finite() {
        //     None => {
        //         // If the start is infinite, then we create an interval that spans
        //         // from -inf to midnight (in the given timezone) of the minimum supported date (excluded)
        //         let Some(new_end) = NaiveDate::MIN
        //             .and_time(NAIVE_TIME_MIDNIGHT)
        //             .and_local_timezone(self.tz.clone())
        //             .earliest()
        //         else {
        //             self.exhausted = true;
        //             return None;
        //         };

        //         let CutResult::Cut(infinite_start, remaining_interval) = self.remaining_interval.cut_at(
        //             new_end.with_timezone(&Utc),
        //             CutType::new(BoundInclusivity::Exclusive, BoundInclusivity::Inclusive),
        //         ) else {
        //             self.exhausted = true;
        //             return None;
        //         };

        //         self.remaining_interval = remaining_interval;
        //         Some(infinite_start)
        //     },
        //     Some(start_bound) => {
        //         todo!()
        //     },
        // }
    }
}

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub struct NaiveDurationRSplit<Tz> {
//     remaining_interval: AbsoluteBoundPair,
//     calendar_anchor_offset: NaiveDuration,
//     splitting_strategy: SplittingStrategy,
//     tz: Tz,
//     exhausted: bool,
// }

// impl<Tz> NaiveDurationRSplit<Tz>
// where
//     Tz: TimeZone,
// {
//     #[must_use]
//     pub fn new<I>(interval: I, calendar_anchor_offset: NaiveDuration, splitting_strategy: SplittingStrategy, tz: Tz) -> Self
//     where
//         I: HasAbsoluteBoundPair,
//     {
//         NaiveDurationRSplit {
//             remaining_interval: interval.abs_bound_pair(),
//             calendar_anchor_offset,
//             splitting_strategy,
//             tz,
//             exhausted: false,
//         }
//     }
// }

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IntervalSplit<I> {
    remaining_interval: I,
    splitter: BoundedRelativeInterval,
}

impl<I> IntervalSplit<I>
where
    I: HasAbsoluteBoundPair,
{
    #[must_use]
    pub fn new(interval: I, splitter: BoundedRelativeInterval) -> Self {
        IntervalSplit {
            remaining_interval: interval,
            splitter,
        }
    }
}

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub struct IntervalRSplit<I> {
//     remaining_interval: I,
//     splitter: BoundedRelativeInterval,
//     splitting_strategy: SplittingStrategy,
// }

// impl<I> IntervalRSplit<I>
// where
//     I: HasAbsoluteBoundPair,
// {
//     #[must_use]
//     pub fn new(interval: I, splitter: BoundedRelativeInterval, splitting_strategy: SplittingStrategy) -> Self {
//         IntervalRSplit {
//             remaining_interval: interval,
//             splitter,
//             splitting_strategy,
//         }
//     }
// }

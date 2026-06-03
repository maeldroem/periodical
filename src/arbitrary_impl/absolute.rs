//! [`Arbitrary`] implementations for items within the
//! [`absolute`](crate::intervals::absolute) module

use std::time::Duration;

use arbitrary::{Arbitrary, Error, Unstructured};
use jiff::Timestamp;

use crate::intervals::absolute::{
    AbsBoundPair,
    AbsEndBound,
    AbsFiniteBoundPos,
    AbsStartBound,
    BoundedAbsInterval,
    HalfBoundedAbsInterval,
};
use crate::intervals::meta::{BoundInclusivity, OpeningDirection};

impl<'a> Arbitrary<'a> for AbsFiniteBoundPos {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let timestamp_range = Timestamp::MIN.as_nanosecond()..=Timestamp::MAX.as_nanosecond();
        let timestamp = Timestamp::from_nanosecond(u.int_in_range(timestamp_range)?).or(Err(Error::IncorrectFormat))?;

        Ok(Self::new_with_inclusivity(timestamp, BoundInclusivity::arbitrary(u)?))
    }
}

impl<'a> Arbitrary<'a> for AbsBoundPair {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start = AbsStartBound::arbitrary(u)?;
        let end = AbsEndBound::arbitrary(u)?;

        // We use AbsBoundPair::new so that if start > end, they get swapped
        // A fuzz test exists to verify that this behavior is correct
        Ok(AbsBoundPair::new(start, end))
    }
}

impl<'a> Arbitrary<'a> for BoundedAbsInterval {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let timestamp_range = Timestamp::MIN.as_nanosecond()..=Timestamp::MAX.as_nanosecond();

        let start_time =
            Timestamp::from_nanosecond(u.int_in_range(timestamp_range)?).or(Err(Error::IncorrectFormat))?;
        let end_time = start_time
            .saturating_add(Duration::from_secs(u64::arbitrary(u)?))
            .or(Err(Error::IncorrectFormat))?;

        if start_time == end_time {
            Ok(BoundedAbsInterval::from_times_incl(
                start_time,
                BoundInclusivity::Inclusive,
                end_time,
                BoundInclusivity::Inclusive,
            ))
        } else {
            Ok(BoundedAbsInterval::from_times_incl(
                start_time,
                BoundInclusivity::arbitrary(u)?,
                end_time,
                BoundInclusivity::arbitrary(u)?,
            ))
        }
    }
}

impl<'a> Arbitrary<'a> for HalfBoundedAbsInterval {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let timestamp_range = Timestamp::MIN.as_nanosecond()..=Timestamp::MAX.as_nanosecond();

        let reference = Timestamp::from_nanosecond(u.int_in_range(timestamp_range)?).or(Err(Error::IncorrectFormat))?;

        Ok(HalfBoundedAbsInterval::new_from_time_and_inclusivity(
            reference,
            BoundInclusivity::arbitrary(u)?,
            OpeningDirection::arbitrary(u)?,
        ))
    }
}

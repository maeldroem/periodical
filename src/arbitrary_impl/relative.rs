//! [`Arbitrary`] implementations for items within the
//! [`relative`](crate::intervals::relative) module

use arbitrary::{Arbitrary, Error, Unstructured};
use jiff::SignedDuration;

use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::relative::{
    BoundedRelInterval,
    HalfBoundedRelInterval,
    RelBoundPair,
    RelEndBound,
    RelFiniteBoundPos,
    RelStartBound,
};

impl<'a> Arbitrary<'a> for RelFiniteBoundPos {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let signed_duration_range = SignedDuration::MIN.as_nanos()..=SignedDuration::MAX.as_nanos();
        let signed_duration = SignedDuration::try_from_nanos_i128(u.int_in_range(signed_duration_range)?)
            .ok_or(Error::IncorrectFormat)?;

        Ok(Self::new_with_incl(
            signed_duration,
            BoundInclusivity::arbitrary(u)?,
        ))
    }
}

impl<'a> Arbitrary<'a> for RelBoundPair {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start = RelStartBound::arbitrary(u)?;
        let end = RelEndBound::arbitrary(u)?;

        // We use RelBoundPair::new so that if start > end, they get swapped
        // A fuzz test exists to verify that this behavior is correct
        Ok(RelBoundPair::new(start, end))
    }
}

impl<'a> Arbitrary<'a> for BoundedRelInterval {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let signed_duration_range = SignedDuration::MIN.as_nanos()..=SignedDuration::MAX.as_nanos();

        let start_offset = SignedDuration::try_from_nanos_i128(u.int_in_range(signed_duration_range.clone())?)
            .ok_or(Error::IncorrectFormat)?;
        let end_offset = SignedDuration::try_from_nanos_i128(u.int_in_range(signed_duration_range)?)
            .ok_or(Error::IncorrectFormat)?;

        if start_offset == end_offset {
            Ok(BoundedRelInterval::from_offsets_incl(
                start_offset,
                BoundInclusivity::Inclusive,
                end_offset,
                BoundInclusivity::Inclusive,
            ))
        } else {
            Ok(BoundedRelInterval::from_offsets_incl(
                start_offset,
                BoundInclusivity::arbitrary(u)?,
                end_offset,
                BoundInclusivity::arbitrary(u)?,
            ))
        }
    }
}

impl<'a> Arbitrary<'a> for HalfBoundedRelInterval {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let signed_duration_range = SignedDuration::MIN.as_nanos()..=SignedDuration::MAX.as_nanos();

        let reference_offset = SignedDuration::try_from_nanos_i128(u.int_in_range(signed_duration_range.clone())?)
            .ok_or(Error::IncorrectFormat)?;

        Ok(HalfBoundedRelInterval::from_offset_incl(
            reference_offset,
            BoundInclusivity::arbitrary(u)?,
            OpeningDirection::arbitrary(u)?,
        ))
    }
}

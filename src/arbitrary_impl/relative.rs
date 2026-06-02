//! [`Arbitrary`] implementations for items within the
//! [`relative`](crate::intervals::relative) module

use arbitrary::{Arbitrary, Error, Unstructured};
use jiff::SignedDuration;

use crate::intervals::meta::{BoundInclusivity, OpeningDirection};
use crate::intervals::relative::{
    BoundedRelativeInterval,
    HalfBoundedRelativeInterval,
    RelativeBoundPair,
    RelativeEndBound,
    RelativeFiniteBoundPosition,
    RelativeStartBound,
};

impl<'a> Arbitrary<'a> for RelativeFiniteBoundPosition {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let signed_duration_range = SignedDuration::MIN.as_nanos()..=SignedDuration::MAX.as_nanos();
        let signed_duration = SignedDuration::try_from_nanos_i128(u.int_in_range(signed_duration_range)?)
            .ok_or(Error::IncorrectFormat)?;

        Ok(Self::new_with_inclusivity(
            signed_duration,
            BoundInclusivity::arbitrary(u)?,
        ))
    }
}

impl<'a> Arbitrary<'a> for RelativeBoundPair {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start = RelativeStartBound::arbitrary(u)?;
        let end = RelativeEndBound::arbitrary(u)?;

        // We use RelativeBoundPair::new so that if start > end, they get swapped
        // A fuzz test exists to verify that this behavior is correct
        Ok(RelativeBoundPair::new(start, end))
    }
}

impl<'a> Arbitrary<'a> for BoundedRelativeInterval {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let signed_duration_range = SignedDuration::MIN.as_nanos()..=SignedDuration::MAX.as_nanos();

        let start_offset = SignedDuration::try_from_nanos_i128(u.int_in_range(signed_duration_range.clone())?)
            .ok_or(Error::IncorrectFormat)?;
        let end_offset = SignedDuration::try_from_nanos_i128(u.int_in_range(signed_duration_range)?)
            .ok_or(Error::IncorrectFormat)?;

        if start_offset == end_offset {
            Ok(BoundedRelativeInterval::from_offsets_and_inclusivities(
                start_offset,
                BoundInclusivity::Inclusive,
                end_offset,
                BoundInclusivity::Inclusive,
            ))
        } else {
            Ok(BoundedRelativeInterval::from_offsets_and_inclusivities(
                start_offset,
                BoundInclusivity::arbitrary(u)?,
                end_offset,
                BoundInclusivity::arbitrary(u)?,
            ))
        }
    }
}

impl<'a> Arbitrary<'a> for HalfBoundedRelativeInterval {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let signed_duration_range = SignedDuration::MIN.as_nanos()..=SignedDuration::MAX.as_nanos();

        let reference_offset = SignedDuration::try_from_nanos_i128(u.int_in_range(signed_duration_range.clone())?)
            .ok_or(Error::IncorrectFormat)?;

        Ok(HalfBoundedRelativeInterval::new_from_offset_and_inclusivity(
            reference_offset,
            BoundInclusivity::arbitrary(u)?,
            OpeningDirection::arbitrary(u)?,
        ))
    }
}

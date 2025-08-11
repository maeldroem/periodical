//! Manual implementations of the [`Arbitrary`] trait on interval types

use arbitrary::{Arbitrary, Unstructured};

use crate::intervals::absolute::{AbsoluteBounds, AbsoluteEndBound, AbsoluteStartBound};
use crate::intervals::relative::{RelativeBounds, RelativeEndBound, RelativeStartBound};

impl<'a> Arbitrary<'a> for AbsoluteBounds {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start = AbsoluteStartBound::arbitrary(u)?;
        let end = AbsoluteEndBound::arbitrary(u)?;

        // We use AbsoluteBounds::new so that if start > end, they get swapped
        // A fuzz test exists to verify that this behavior is correct
        Ok(AbsoluteBounds::new(start, end))
    }
}

impl<'a> Arbitrary<'a> for RelativeBounds {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let start = RelativeStartBound::arbitrary(u)?;
        let end = RelativeEndBound::arbitrary(u)?;

        // We use RelativeBounds::new so that if start > end, they get swapped
        // A fuzz test exists to verify that this behavior is correct
        Ok(RelativeBounds::new(start, end))
    }
}

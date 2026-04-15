//! Precision change for relative bounds

use jiff::SignedDuration;

use crate::ops::Precision;

/// Ability to precise relative bounds
///
/// The precision itself is defined by [`Precision`].
pub trait PreciseRelativeBound {
    type PrecisedBoundOutput;

    #[must_use]
    fn precise_bounds(&self, precision: Precision) -> Self::PrecisedBoundOutput;

    #[must_use]
    fn precise_bound_with_base_offset(&self, precision: Precision, base: SignedDuration) -> Self::PrecisedBoundOutput;
}

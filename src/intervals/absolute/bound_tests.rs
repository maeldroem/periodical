use std::error::Error;

use jiff::Timestamp;

use super::bound::*;
use crate::intervals::absolute::{AbsEndBound, AbsFiniteBoundPos, AbsStartBound};
use crate::intervals::meta::BoundInclusivity;

#[test]
fn is_start() {
    assert!(AbsStartBound::InfinitePast.to_bound().is_start());
    assert!(!AbsEndBound::InfiniteFuture.to_bound().is_start());
}

#[test]
fn is_end() {
    assert!(!AbsStartBound::InfinitePast.to_bound().is_end());
    assert!(AbsEndBound::InfiniteFuture.to_bound().is_end());
}

#[test]
fn start() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
            .start(),
        Some(AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
    );
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
            .start(),
        None,
    );
    Ok(())
}

#[test]
fn end() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
            .end(),
        None,
    );
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
            .end(),
        Some(AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
    );
    Ok(())
}

#[test]
fn start_inf_past_opposite() {
    assert_eq!(AbsStartBound::InfinitePast.to_bound().opposite(), None);
}

#[test]
fn start_finite_opposite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
            .opposite(),
        Some(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
            .to_bound()
        ),
    );
    Ok(())
}

#[test]
fn end_inf_future_opposite() {
    assert_eq!(AbsEndBound::InfiniteFuture.to_bound().opposite(), None);
}

#[test]
fn end_finite_opposite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
            .opposite(),
        Some(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
            .to_bound()
        ),
    );
    Ok(())
}

#[test]
fn equality() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound(),
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
    );
    assert_eq!(
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound(),
        AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
    );

    Ok(())
}

#[test]
fn from_absolute_start_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBound::from(AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
        AbsBound::Start(AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
    );
    Ok(())
}

#[test]
fn from_absolute_end_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsBound::from(AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
        AbsBound::End(AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
    );
    Ok(())
}

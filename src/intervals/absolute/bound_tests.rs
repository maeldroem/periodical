use std::error::Error;

use jiff::Timestamp;

use crate::intervals::absolute::{AbsoluteEndBound, AbsoluteFiniteBound, AbsoluteStartBound};
use crate::intervals::meta::BoundInclusivity;

use super::bound::*;

#[test]
fn is_start() {
    assert!(AbsoluteStartBound::InfinitePast.to_bound().is_start());
    assert!(!AbsoluteEndBound::InfiniteFuture.to_bound().is_start());
}

#[test]
fn is_end() {
    assert!(!AbsoluteStartBound::InfinitePast.to_bound().is_end());
    assert!(AbsoluteEndBound::InfiniteFuture.to_bound().is_end());
}

#[test]
fn start() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
            .start(),
        Some(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
    );
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
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
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
            .end(),
        None,
    );
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
            .end(),
        Some(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
    );
    Ok(())
}

#[test]
fn start_inf_past_opposite() {
    assert_eq!(AbsoluteStartBound::InfinitePast.to_bound().opposite(), None);
}

#[test]
fn start_finite_opposite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .to_bound()
            .opposite(),
        Some(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ).to_end_bound().to_bound()),
    );
    Ok(())
}

#[test]
fn end_inf_future_opposite() {
    assert_eq!(AbsoluteEndBound::InfiniteFuture.to_bound().opposite(), None);
}

#[test]
fn end_finite_opposite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_end_bound()
            .to_bound()
            .opposite(),
        Some(AbsoluteFiniteBound::new_with_inclusivity(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        ).to_start_bound().to_bound()),
    );
    Ok(())
}

#[test]
fn from_absolute_start_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBound::from(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
        AbsoluteBound::Start(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
    );
    Ok(())
}

#[test]
fn from_absolute_end_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsoluteBound::from(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
        AbsoluteBound::End(AbsoluteFiniteBound::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_end_bound()),
    );
    Ok(())
}

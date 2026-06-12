use std::cmp::Ordering;
use std::error::Error;
use std::ops::Bound;

use jiff::Timestamp;

use super::start_bound::*;
use crate::intervals::absolute::{AbsBound, AbsEndBound, AbsFiniteBoundPos};
use crate::intervals::meta::BoundInclusivity;

#[test]
fn to_bound() -> Result<(), Box<dyn Error>> {
    let start_bound = AbsFiniteBoundPos::new("2026-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound();

    assert_eq!(start_bound.to_bound(), AbsBound::Start(start_bound),);
    Ok(())
}

#[test]
fn is_finite() -> Result<(), Box<dyn Error>> {
    assert!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .is_finite()
    );
    assert!(!AbsStartBound::InfinitePast.is_finite());
    Ok(())
}

#[test]
fn is_infinite_past() -> Result<(), Box<dyn Error>> {
    assert!(
        !AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .is_infinite_past()
    );
    assert!(AbsStartBound::InfinitePast.is_infinite_past());
    Ok(())
}

#[test]
fn finite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .finite(),
        Some(AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_finite_start_bound()),
    );
    assert_eq!(AbsStartBound::InfinitePast.finite(), None);
    Ok(())
}

#[test]
fn opposite() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
            .to_start_bound()
            .opposite(),
        Some(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_end_bound()
        ),
    );
    assert_eq!(AbsStartBound::InfinitePast.opposite(), None);
    Ok(())
}

mod ord {
    use super::*;

    #[test]
    fn inf_inf() {
        assert_eq!(
            AbsStartBound::InfinitePast.cmp(&AbsStartBound::InfinitePast),
            Ordering::Equal
        );
    }

    #[test]
    fn inf_finite() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsStartBound::InfinitePast
                .cmp(&AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
            Ordering::Less,
        );
        Ok(())
    }

    #[test]
    fn finite_inf() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .to_start_bound()
                .cmp(&AbsStartBound::InfinitePast),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn different_times_greater() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?)
                .to_start_bound()
                .cmp(&AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn different_times_less() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new("2025-01-01 00:00:00Z".parse::<Timestamp>()?)
                .to_start_bound()
                .cmp(&AbsFiniteBoundPos::new("2025-01-02 00:00:00Z".parse::<Timestamp>()?).to_start_bound()),
            Ordering::Less,
        );
        Ok(())
    }

    #[test]
    fn same_times_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
            .cmp(
                &AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
            ),
            Ordering::Equal,
        );
        Ok(())
    }

    #[test]
    fn same_times_exclusive_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_start_bound()
            .cmp(
                &AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound()
            ),
            Ordering::Greater,
        );
        Ok(())
    }

    #[test]
    fn same_times_inclusive_exclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound()
            .cmp(
                &AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Exclusive,
                )
                .to_start_bound()
            ),
            Ordering::Less,
        );
        Ok(())
    }

    #[test]
    fn same_times_inclusive_bounds() -> Result<(), Box<dyn Error>> {
        assert_eq!(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Inclusive,
            )
            .to_start_bound()
            .cmp(
                &AbsFiniteBoundPos::new_with_incl(
                    "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                    BoundInclusivity::Inclusive,
                )
                .to_start_bound()
            ),
            Ordering::Equal,
        );
        Ok(())
    }
}

#[test]
fn from_absolute_finite_bound_position() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsStartBound::from(AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )),
        AbsStartBound::Finite(
            AbsFiniteBoundPos::new_with_incl(
                "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive,
            )
            .to_finite_start_bound()
        ),
    );
    Ok(())
}

#[test]
fn from_opt_timestamp() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsStartBound::from(Some("2026-01-01 08:00:00Z".parse::<Timestamp>()?)),
        AbsFiniteBoundPos::new("2026-01-01 08:00:00Z".parse::<Timestamp>()?).to_start_bound()
    );
    assert_eq!(AbsStartBound::from(None::<Timestamp>), AbsStartBound::InfinitePast);
    Ok(())
}

#[test]
fn from_opt_timestamp_inclusivity() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsStartBound::from(Some((
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        ))),
        AbsFiniteBoundPos::new_with_incl(
            "2026-01-01 08:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        )
        .to_start_bound()
    );
    assert_eq!(
        AbsStartBound::from(None::<(Timestamp, BoundInclusivity)>),
        AbsStartBound::InfinitePast
    );
    Ok(())
}

#[test]
fn from_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsStartBound::from(Bound::Included("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Inclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(
        AbsStartBound::from(Bound::Excluded("2025-01-01 00:00:00Z".parse::<Timestamp>()?)),
        AbsFiniteBoundPos::new_with_incl(
            "2025-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive,
        )
        .to_start_bound(),
    );
    assert_eq!(AbsStartBound::from(Bound::Unbounded), AbsStartBound::InfinitePast);

    Ok(())
}

#[test]
fn try_from_abs_bound() -> Result<(), Box<dyn Error>> {
    assert_eq!(
        AbsStartBound::try_from(
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_start_bound()
            .to_bound()
        ),
        Ok(AbsFiniteBoundPos::new_with_incl(
            "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
            BoundInclusivity::Exclusive
        )
        .to_start_bound())
    );
    assert_eq!(
        AbsStartBound::try_from(AbsStartBound::InfinitePast.to_bound()),
        Ok(AbsStartBound::InfinitePast)
    );

    assert_eq!(
        AbsStartBound::try_from(
            AbsFiniteBoundPos::new_with_incl(
                "2026-01-01 00:00:00Z".parse::<Timestamp>()?,
                BoundInclusivity::Exclusive
            )
            .to_end_bound()
            .to_bound()
        ),
        Err(AbsStartBoundTryFromAbsBoundError)
    );
    assert_eq!(
        AbsStartBound::try_from(AbsEndBound::InfiniteFuture.to_bound()),
        Err(AbsStartBoundTryFromAbsBoundError)
    );

    Ok(())
}

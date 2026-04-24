use std::error::Error;
use std::time::Duration;

use jiff::tz::TimeZone;
use jiff::{SignedDuration, Zoned};

use crate::ops::*;

mod precision {
    use super::*;

    const U_NANOS_NEAR_UP_FIVE_MS: u128 = 7_104_194_555;
    const U_NANOS_NEAR_DOWN_FIVE_MS: u128 = 7_102_194_555;
    const U_NANOS_TIE_FIVE_MS: u128 = 7_102_500_000;
    const U_NANOS_UP_FIVE_MS: u128 = 7_105_000_000;
    const U_NANOS_DOWN_FIVE_MS: u128 = 7_100_000_000;

    const S_NANOS_POS_NEAR_UP_FIVE_MS: i128 = 7_104_194_555;
    const S_NANOS_POS_NEAR_DOWN_FIVE_MS: i128 = 7_102_194_555;
    const S_NANOS_POS_TIE_FIVE_MS: i128 = 7_102_500_000;
    const S_NANOS_POS_UP_FIVE_MS: i128 = 7_105_000_000;
    const S_NANOS_POS_DOWN_FIVE_MS: i128 = 7_100_000_000;

    const S_NANOS_NEG_NEAR_UP_FIVE_MS: i128 = -7_102_194_555;
    const S_NANOS_NEG_NEAR_DOWN_FIVE_MS: i128 = -7_104_194_555;
    const S_NANOS_NEG_TIE_FIVE_MS: i128 = -7_102_500_000;
    const S_NANOS_NEG_UP_FIVE_MS: i128 = -7_100_000_000;
    const S_NANOS_NEG_DOWN_FIVE_MS: i128 = -7_105_000_000;

    const U_DUR_FIVE_MS: Duration = Duration::from_millis(5);
    const U_DUR_FIVE_MINS: Duration = Duration::from_mins(5);

    const U_DUR_NEAR_UP_FIVE_MINS: Duration = Duration::from_secs(822); // 13m 42s
    const U_DUR_NEAR_DOWN_FIVE_MINS: Duration = Duration::from_secs(653); // 10m 53s
    const U_DUR_TIE_FIVE_MINS: Duration = Duration::from_secs(750); // 12m 30s
    const U_DUR_UP_FIVE_MINS: Duration = Duration::from_mins(15);
    const U_DUR_DOWN_FIVE_MINS: Duration = Duration::from_mins(10);

    const S_DUR_POS_NEAR_UP_FIVE_MINS: SignedDuration = SignedDuration::from_secs(822); // 13m 42s
    const S_DUR_POS_NEAR_DOWN_FIVE_MINS: SignedDuration = SignedDuration::from_secs(653); // 10m 53s
    const S_DUR_POS_TIE_FIVE_MINS: SignedDuration = SignedDuration::from_secs(750); // 12m 30s
    const S_DUR_POS_UP_FIVE_MINS: SignedDuration = SignedDuration::from_mins(15);
    const S_DUR_POS_DOWN_FIVE_MINS: SignedDuration = SignedDuration::from_mins(10);

    const S_DUR_NEG_NEAR_UP_FIVE_MINS: SignedDuration = SignedDuration::from_secs(-653); // -10m 53s
    const S_DUR_NEG_NEAR_DOWN_FIVE_MINS: SignedDuration = SignedDuration::from_secs(-822); // -13m 42s
    const S_DUR_NEG_TIE_FIVE_MINS: SignedDuration = SignedDuration::from_secs(-750); // -12m 30s
    const S_DUR_NEG_UP_FIVE_MINS: SignedDuration = SignedDuration::from_mins(-10);
    const S_DUR_NEG_DOWN_FIVE_MINS: SignedDuration = SignedDuration::from_mins(-15);

    mod create {
        use super::*;

        #[test]
        fn precision_mode_unchecked_with_precision_parity_with_precision_unchecked_new() {
            assert_eq!(
                PrecisionMode::ToFuture.unchecked_with_precision(U_DUR_FIVE_MINS),
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture),
            );
            assert_eq!(
                PrecisionMode::ToPast.unchecked_with_precision(U_DUR_FIVE_MINS),
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToPast),
            );
            assert_eq!(
                PrecisionMode::ToNearest.unchecked_with_precision(U_DUR_FIVE_MINS),
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest),
            );
            assert_eq!(
                PrecisionMode::ToFuture.unchecked_with_precision(Duration::ZERO),
                Precision::unchecked_new(Duration::ZERO, PrecisionMode::ToFuture),
            );
            assert_eq!(
                PrecisionMode::ToPast.unchecked_with_precision(Duration::ZERO),
                Precision::unchecked_new(Duration::ZERO, PrecisionMode::ToPast),
            );
            assert_eq!(
                PrecisionMode::ToNearest.unchecked_with_precision(Duration::ZERO),
                Precision::unchecked_new(Duration::ZERO, PrecisionMode::ToNearest),
            );
        }

        #[test]
        fn precision_mode_with_precision_parity_with_precision_new() {
            assert_eq!(
                PrecisionMode::ToFuture.with_precision(U_DUR_FIVE_MINS),
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture),
            );
            assert_eq!(
                PrecisionMode::ToPast.with_precision(U_DUR_FIVE_MINS),
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast),
            );
            assert_eq!(
                PrecisionMode::ToNearest.with_precision(U_DUR_FIVE_MINS),
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest),
            );
            assert_eq!(
                PrecisionMode::ToFuture.with_precision(Duration::ZERO),
                Precision::new(Duration::ZERO, PrecisionMode::ToFuture),
            );
            assert_eq!(
                PrecisionMode::ToPast.with_precision(Duration::ZERO),
                Precision::new(Duration::ZERO, PrecisionMode::ToPast),
            );
            assert_eq!(
                PrecisionMode::ToNearest.with_precision(Duration::ZERO),
                Precision::new(Duration::ZERO, PrecisionMode::ToNearest),
            );
        }

        #[test]
        fn precision_unchecked_new_accepts_precision_zero() {
            let _ = Precision::unchecked_new(Duration::ZERO, PrecisionMode::ToFuture);
            let _ = Precision::unchecked_new(Duration::ZERO, PrecisionMode::ToPast);
            let _ = Precision::unchecked_new(Duration::ZERO, PrecisionMode::ToNearest);
        }

        #[test]
        fn precision_new_rejects_precision_zero() {
            assert!(Precision::new(Duration::ZERO, PrecisionMode::ToFuture).is_err());
            assert!(Precision::new(Duration::ZERO, PrecisionMode::ToPast).is_err());
            assert!(Precision::new(Duration::ZERO, PrecisionMode::ToNearest).is_err());
        }

        #[test]
        fn precision_new_accepts_non_zero_precisions() {
            assert!(Precision::new(Duration::from_nanos(1), PrecisionMode::ToFuture).is_ok());
            assert!(Precision::new(Duration::from_nanos(1), PrecisionMode::ToPast).is_ok());
            assert!(Precision::new(Duration::from_nanos(1), PrecisionMode::ToNearest).is_ok());

            assert!(Precision::new(Duration::from_mins(15), PrecisionMode::ToFuture).is_ok());
            assert!(Precision::new(Duration::from_mins(15), PrecisionMode::ToPast).is_ok());
            assert!(Precision::new(Duration::from_mins(15), PrecisionMode::ToNearest).is_ok());

            assert!(Precision::new(Duration::MAX, PrecisionMode::ToFuture).is_ok());
            assert!(Precision::new(Duration::MAX, PrecisionMode::ToPast).is_ok());
            assert!(Precision::new(Duration::MAX, PrecisionMode::ToNearest).is_ok());
        }
    }

    mod precise_unsigned_nanos {
        use super::*;

        #[test]
        fn to_future_zero() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToFuture).precise_unsigned_nanos(0),
                0,
            );
        }

        #[test]
        fn to_future_non_zero() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToFuture)
                    .precise_unsigned_nanos(U_NANOS_NEAR_UP_FIVE_MS),
                U_NANOS_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_future_non_zero_on_anchor() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToFuture)
                    .precise_unsigned_nanos(U_NANOS_UP_FIVE_MS),
                U_NANOS_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_past_zero() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToPast).precise_unsigned_nanos(0),
                0,
            );
        }

        #[test]
        fn to_past_non_zero() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToPast)
                    .precise_unsigned_nanos(U_NANOS_NEAR_UP_FIVE_MS),
                U_NANOS_DOWN_FIVE_MS,
            );
        }

        #[test]
        fn to_past_non_zero_on_anchor() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToPast)
                    .precise_unsigned_nanos(U_NANOS_UP_FIVE_MS),
                U_NANOS_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_nearest_zero() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToNearest).precise_unsigned_nanos(0),
                0,
            );
        }

        #[test]
        fn to_nearest_non_zero_to_future() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToNearest)
                    .precise_unsigned_nanos(U_NANOS_NEAR_UP_FIVE_MS),
                U_NANOS_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_nearest_non_zero_to_past() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToNearest)
                    .precise_unsigned_nanos(U_NANOS_NEAR_DOWN_FIVE_MS),
                U_NANOS_DOWN_FIVE_MS,
            );
        }

        #[test]
        fn to_nearest_non_zero_tie() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToNearest)
                    .precise_unsigned_nanos(U_NANOS_TIE_FIVE_MS),
                U_NANOS_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_nearest_non_zero_on_anchor() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToNearest)
                    .precise_unsigned_nanos(U_NANOS_UP_FIVE_MS),
                U_NANOS_UP_FIVE_MS,
            );
        }
    }

    mod precise_signed_nanos {
        use super::*;

        #[test]
        fn to_future_zero() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToFuture).precise_signed_nanos(0),
                0,
            );
        }

        #[test]
        fn to_future_positive() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToFuture)
                    .precise_signed_nanos(S_NANOS_POS_NEAR_DOWN_FIVE_MS),
                S_NANOS_POS_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_future_positive_on_anchor() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToFuture)
                    .precise_signed_nanos(S_NANOS_POS_UP_FIVE_MS),
                S_NANOS_POS_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_future_negative() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToFuture)
                    .precise_signed_nanos(S_NANOS_NEG_NEAR_DOWN_FIVE_MS),
                S_NANOS_NEG_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_future_negative_on_anchor() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToFuture)
                    .precise_signed_nanos(S_NANOS_NEG_UP_FIVE_MS),
                S_NANOS_NEG_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_past_zero() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToPast).precise_signed_nanos(0),
                0,
            );
        }

        #[test]
        fn to_past_positive() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToPast)
                    .precise_signed_nanos(S_NANOS_POS_NEAR_UP_FIVE_MS),
                S_NANOS_POS_DOWN_FIVE_MS,
            );
        }

        #[test]
        fn to_past_positive_on_anchor() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToPast)
                    .precise_signed_nanos(S_NANOS_POS_UP_FIVE_MS),
                S_NANOS_POS_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_past_negative() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToPast)
                    .precise_signed_nanos(S_NANOS_NEG_NEAR_UP_FIVE_MS),
                S_NANOS_NEG_DOWN_FIVE_MS,
            );
        }

        #[test]
        fn to_past_negative_anchor() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToPast)
                    .precise_signed_nanos(S_NANOS_NEG_UP_FIVE_MS),
                S_NANOS_NEG_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_nearest_zero() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToNearest).precise_signed_nanos(0),
                0,
            );
        }

        #[test]
        fn to_nearest_positive_to_future() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToNearest)
                    .precise_signed_nanos(S_NANOS_POS_NEAR_UP_FIVE_MS),
                S_NANOS_POS_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_nearest_positive_to_past() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToNearest)
                    .precise_signed_nanos(S_NANOS_POS_NEAR_DOWN_FIVE_MS),
                S_NANOS_POS_DOWN_FIVE_MS,
            );
        }

        #[test]
        fn to_nearest_positive_tie() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToNearest)
                    .precise_signed_nanos(S_NANOS_POS_TIE_FIVE_MS),
                S_NANOS_POS_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_nearest_positive_on_anchor() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToNearest)
                    .precise_signed_nanos(S_NANOS_POS_UP_FIVE_MS),
                S_NANOS_POS_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_nearest_negative_to_future() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToNearest)
                    .precise_signed_nanos(S_NANOS_NEG_NEAR_UP_FIVE_MS),
                S_NANOS_NEG_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_nearest_negative_to_past() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToNearest)
                    .precise_signed_nanos(S_NANOS_NEG_NEAR_DOWN_FIVE_MS),
                S_NANOS_NEG_DOWN_FIVE_MS,
            );
        }

        #[test]
        fn to_nearest_negative_tie() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToNearest)
                    .precise_signed_nanos(S_NANOS_NEG_TIE_FIVE_MS),
                S_NANOS_NEG_UP_FIVE_MS,
            );
        }

        #[test]
        fn to_nearest_negative_on_anchor() {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MS, PrecisionMode::ToNearest)
                    .precise_signed_nanos(S_NANOS_NEG_UP_FIVE_MS),
                S_NANOS_NEG_UP_FIVE_MS,
            );
        }
    }

    mod precise_duration {
        use super::*;

        #[test]
        fn to_future_zero() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture).precise_duration(Duration::ZERO)?,
                Duration::ZERO,
            );
            Ok(())
        }

        #[test]
        fn to_future_non_zero() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)
                    .precise_duration(U_DUR_NEAR_DOWN_FIVE_MINS)?,
                U_DUR_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_future_non_zero_on_anchor() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)
                    .precise_duration(U_DUR_UP_FIVE_MINS)?,
                U_DUR_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_past_zero() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToPast).precise_duration(Duration::ZERO)?,
                Duration::ZERO,
            );
            Ok(())
        }

        #[test]
        fn to_past_non_zero() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)
                    .precise_duration(U_DUR_NEAR_UP_FIVE_MINS)?,
                U_DUR_DOWN_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_past_non_zero_on_anchor() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)
                    .precise_duration(U_DUR_UP_FIVE_MINS)?,
                U_DUR_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_nearest_zero() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest).precise_duration(Duration::ZERO)?,
                Duration::ZERO,
            );
            Ok(())
        }

        #[test]
        fn to_nearest_non_zero_to_future() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)
                    .precise_duration(U_DUR_NEAR_UP_FIVE_MINS)?,
                U_DUR_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_nearest_non_zero_to_past() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)
                    .precise_duration(U_DUR_NEAR_DOWN_FIVE_MINS)?,
                U_DUR_DOWN_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_nearest_non_zero_tie() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)
                    .precise_duration(U_DUR_TIE_FIVE_MINS)?,
                U_DUR_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_nearest_non_zero_on_anchor() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)
                    .precise_duration(U_DUR_UP_FIVE_MINS)?,
                U_DUR_UP_FIVE_MINS,
            );
            Ok(())
        }
    }

    mod precise_duration_with_base_offset {
        use super::*;

        #[test]
        fn zero_duration_zero_base() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)?
                    .precise_duration_with_base_offset(Duration::ZERO, Duration::ZERO)?,
                Duration::ZERO,
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)?
                    .precise_duration_with_base_offset(Duration::ZERO, Duration::ZERO)?,
                Duration::ZERO,
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?
                    .precise_duration_with_base_offset(Duration::ZERO, Duration::ZERO)?,
                Duration::ZERO,
            );

            Ok(())
        }

        #[test]
        fn after_base() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)?
                    .precise_duration_with_base_offset(Duration::from_mins(18), Duration::from_mins(2))?,
                Duration::from_mins(22),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)?
                    .precise_duration_with_base_offset(Duration::from_mins(20), Duration::from_mins(2))?,
                Duration::from_mins(17),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?
                    .precise_duration_with_base_offset(Duration::from_mins(13), Duration::from_mins(2))?,
                Duration::from_mins(12),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?
                    .precise_duration_with_base_offset(Duration::from_mins(16), Duration::from_mins(2))?,
                Duration::from_mins(17),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?.precise_duration_with_base_offset(
                    Duration::from_mins(14) + Duration::from_secs(30),
                    Duration::from_mins(2)
                )?,
                Duration::from_mins(17),
            );

            Ok(())
        }

        #[test]
        fn on_base() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)?
                    .precise_duration_with_base_offset(Duration::from_mins(2), Duration::from_mins(2))?,
                Duration::from_mins(2),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)?
                    .precise_duration_with_base_offset(Duration::from_mins(2), Duration::from_mins(2))?,
                Duration::from_mins(2),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?
                    .precise_duration_with_base_offset(Duration::from_mins(2), Duration::from_mins(2))?,
                Duration::from_mins(2),
            );

            Ok(())
        }

        #[test]
        fn before_base() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)?
                    .precise_duration_with_base_offset(Duration::from_mins(15), Duration::from_mins(27)),
                Err(PrecisionOutOfRangeError),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)?
                    .precise_duration_with_base_offset(Duration::from_mins(15), Duration::from_mins(27)),
                Err(PrecisionOutOfRangeError),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?
                    .precise_duration_with_base_offset(Duration::from_mins(15), Duration::from_mins(27)),
                Err(PrecisionOutOfRangeError),
            );

            Ok(())
        }
    }

    mod precise_duration_with_base_offset_via_signed {
        use super::*;

        #[test]
        fn zero_duration_zero_base() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)?
                    .precise_duration_with_base_offset_via_signed(Duration::ZERO, Duration::ZERO)?,
                Duration::ZERO,
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)?
                    .precise_duration_with_base_offset_via_signed(Duration::ZERO, Duration::ZERO)?,
                Duration::ZERO,
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?
                    .precise_duration_with_base_offset_via_signed(Duration::ZERO, Duration::ZERO)?,
                Duration::ZERO,
            );

            Ok(())
        }

        #[test]
        fn after_base() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)?
                    .precise_duration_with_base_offset_via_signed(Duration::from_mins(18), Duration::from_mins(2))?,
                Duration::from_mins(22),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)?
                    .precise_duration_with_base_offset_via_signed(Duration::from_mins(20), Duration::from_mins(2))?,
                Duration::from_mins(17),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?
                    .precise_duration_with_base_offset_via_signed(Duration::from_mins(13), Duration::from_mins(2))?,
                Duration::from_mins(12),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?
                    .precise_duration_with_base_offset_via_signed(Duration::from_mins(16), Duration::from_mins(2))?,
                Duration::from_mins(17),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?
                    .precise_duration_with_base_offset_via_signed(
                        Duration::from_mins(14) + Duration::from_secs(30),
                        Duration::from_mins(2)
                    )?,
                Duration::from_mins(17),
            );

            Ok(())
        }

        #[test]
        fn on_base() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)?
                    .precise_duration_with_base_offset_via_signed(Duration::from_mins(2), Duration::from_mins(2))?,
                Duration::from_mins(2),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)?
                    .precise_duration_with_base_offset_via_signed(Duration::from_mins(2), Duration::from_mins(2))?,
                Duration::from_mins(2),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?
                    .precise_duration_with_base_offset_via_signed(Duration::from_mins(2), Duration::from_mins(2))?,
                Duration::from_mins(2),
            );

            Ok(())
        }

        #[test]
        fn before_base() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)?
                    .precise_duration_with_base_offset_via_signed(Duration::from_mins(15), Duration::from_mins(27))?,
                Duration::from_mins(17),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)?
                    .precise_duration_with_base_offset_via_signed(Duration::from_mins(15), Duration::from_mins(27))?,
                Duration::from_mins(12),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?
                    .precise_duration_with_base_offset_via_signed(Duration::from_mins(15), Duration::from_mins(27))?,
                Duration::from_mins(17),
            );

            Ok(())
        }

        #[test]
        fn duration_too_large_for_signed_duration() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)?
                    .precise_duration_with_base_offset_via_signed(Duration::MAX, Duration::from_mins(2)),
                Err(PrecisionOutOfRangeError)
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)?
                    .precise_duration_with_base_offset_via_signed(Duration::MAX, Duration::from_mins(2)),
                Err(PrecisionOutOfRangeError)
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?
                    .precise_duration_with_base_offset_via_signed(Duration::MAX, Duration::from_mins(2)),
                Err(PrecisionOutOfRangeError)
            );

            Ok(())
        }

        #[test]
        fn base_too_large_for_signed_duration() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)?
                    .precise_duration_with_base_offset_via_signed(Duration::from_mins(27), Duration::MAX),
                Err(PrecisionOutOfRangeError)
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)?
                    .precise_duration_with_base_offset_via_signed(Duration::from_mins(27), Duration::MAX),
                Err(PrecisionOutOfRangeError)
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?
                    .precise_duration_with_base_offset_via_signed(Duration::from_mins(27), Duration::MAX),
                Err(PrecisionOutOfRangeError)
            );

            Ok(())
        }
    }

    mod precise_signed_duration {
        use super::*;

        #[test]
        fn to_future_zero() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)
                    .precise_signed_duration(SignedDuration::ZERO)?,
                SignedDuration::ZERO,
            );
            Ok(())
        }

        #[test]
        fn to_future_positive() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)
                    .precise_signed_duration(S_DUR_POS_NEAR_DOWN_FIVE_MINS)?,
                S_DUR_POS_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_future_positive_on_anchor() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)
                    .precise_signed_duration(S_DUR_POS_UP_FIVE_MINS)?,
                S_DUR_POS_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_future_negative() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)
                    .precise_signed_duration(S_DUR_NEG_NEAR_DOWN_FIVE_MINS)?,
                S_DUR_NEG_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_future_negative_on_anchor() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)
                    .precise_signed_duration(S_DUR_NEG_UP_FIVE_MINS)?,
                S_DUR_NEG_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_past_zero() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)
                    .precise_signed_duration(SignedDuration::ZERO)?,
                SignedDuration::ZERO,
            );
            Ok(())
        }

        #[test]
        fn to_past_positive() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)
                    .precise_signed_duration(S_DUR_POS_NEAR_UP_FIVE_MINS)?,
                S_DUR_POS_DOWN_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_past_positive_on_anchor() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)
                    .precise_signed_duration(S_DUR_POS_UP_FIVE_MINS)?,
                S_DUR_POS_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_past_negative() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)
                    .precise_signed_duration(S_DUR_NEG_NEAR_UP_FIVE_MINS)?,
                S_DUR_NEG_DOWN_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_past_negative_anchor() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)
                    .precise_signed_duration(S_DUR_NEG_UP_FIVE_MINS)?,
                S_DUR_NEG_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_nearest_zero() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)
                    .precise_signed_duration(SignedDuration::ZERO)?,
                SignedDuration::ZERO,
            );
            Ok(())
        }

        #[test]
        fn to_nearest_positive_to_future() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)
                    .precise_signed_duration(S_DUR_POS_NEAR_UP_FIVE_MINS)?,
                S_DUR_POS_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_nearest_positive_to_past() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)
                    .precise_signed_duration(S_DUR_POS_NEAR_DOWN_FIVE_MINS)?,
                S_DUR_POS_DOWN_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_nearest_positive_tie() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)
                    .precise_signed_duration(S_DUR_POS_TIE_FIVE_MINS)?,
                S_DUR_POS_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_nearest_positive_on_anchor() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)
                    .precise_signed_duration(S_DUR_POS_UP_FIVE_MINS)?,
                S_DUR_POS_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_nearest_negative_to_future() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)
                    .precise_signed_duration(S_DUR_NEG_NEAR_UP_FIVE_MINS)?,
                S_DUR_NEG_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_nearest_negative_to_past() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)
                    .precise_signed_duration(S_DUR_NEG_NEAR_DOWN_FIVE_MINS)?,
                S_DUR_NEG_DOWN_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_nearest_negative_tie() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)
                    .precise_signed_duration(S_DUR_NEG_TIE_FIVE_MINS)?,
                S_DUR_NEG_UP_FIVE_MINS,
            );
            Ok(())
        }

        #[test]
        fn to_nearest_negative_on_anchor() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)
                    .precise_signed_duration(S_DUR_NEG_UP_FIVE_MINS)?,
                S_DUR_NEG_UP_FIVE_MINS,
            );
            Ok(())
        }
    }

    mod precise_signed_duration_with_base_offset {
        use super::*;

        #[test]
        fn zero_duration_zero_base() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)?
                    .precise_signed_duration_with_base_offset(SignedDuration::ZERO, SignedDuration::ZERO)?,
                SignedDuration::ZERO,
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)?
                    .precise_signed_duration_with_base_offset(SignedDuration::ZERO, SignedDuration::ZERO)?,
                SignedDuration::ZERO,
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?
                    .precise_signed_duration_with_base_offset(SignedDuration::ZERO, SignedDuration::ZERO)?,
                SignedDuration::ZERO,
            );

            Ok(())
        }

        #[test]
        fn after_base() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)?.precise_signed_duration_with_base_offset(
                    SignedDuration::from_mins(18),
                    SignedDuration::from_mins(-3)
                )?,
                SignedDuration::from_mins(22),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)?.precise_signed_duration_with_base_offset(
                    SignedDuration::from_mins(20),
                    SignedDuration::from_mins(-3)
                )?,
                SignedDuration::from_mins(17),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?.precise_signed_duration_with_base_offset(
                    SignedDuration::from_mins(13),
                    SignedDuration::from_mins(-3)
                )?,
                SignedDuration::from_mins(12),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?.precise_signed_duration_with_base_offset(
                    SignedDuration::from_mins(16),
                    SignedDuration::from_mins(-3)
                )?,
                SignedDuration::from_mins(17),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?.precise_signed_duration_with_base_offset(
                    SignedDuration::from_mins(14) + SignedDuration::from_secs(30),
                    SignedDuration::from_mins(-3)
                )?,
                SignedDuration::from_mins(17),
            );

            Ok(())
        }

        #[test]
        fn on_base() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)?.precise_signed_duration_with_base_offset(
                    SignedDuration::from_mins(-2),
                    SignedDuration::from_mins(-2)
                )?,
                SignedDuration::from_mins(-2),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)?.precise_signed_duration_with_base_offset(
                    SignedDuration::from_mins(-2),
                    SignedDuration::from_mins(-2)
                )?,
                SignedDuration::from_mins(-2),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?.precise_signed_duration_with_base_offset(
                    SignedDuration::from_mins(-2),
                    SignedDuration::from_mins(-2)
                )?,
                SignedDuration::from_mins(-2),
            );

            Ok(())
        }

        #[test]
        fn before_base() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToFuture)?.precise_signed_duration_with_base_offset(
                    SignedDuration::from_mins(-18),
                    SignedDuration::from_mins(-2)
                )?,
                SignedDuration::from_mins(-17),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToPast)?.precise_signed_duration_with_base_offset(
                    SignedDuration::from_mins(-18),
                    SignedDuration::from_mins(-2)
                )?,
                SignedDuration::from_mins(-22),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?.precise_signed_duration_with_base_offset(
                    SignedDuration::from_mins(-18),
                    SignedDuration::from_mins(-2)
                )?,
                SignedDuration::from_mins(-17),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?.precise_signed_duration_with_base_offset(
                    SignedDuration::from_mins(-16),
                    SignedDuration::from_mins(-2)
                )?,
                SignedDuration::from_mins(-17),
            );
            assert_eq!(
                Precision::new(U_DUR_FIVE_MINS, PrecisionMode::ToNearest)?.precise_signed_duration_with_base_offset(
                    SignedDuration::from_mins(-14) + SignedDuration::from_secs(-30),
                    SignedDuration::from_mins(-2)
                )?,
                SignedDuration::from_mins(-12),
            );

            Ok(())
        }
    }

    mod precise_time {
        use super::*;

        #[test]
        fn simple_rounding() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(Duration::from_hours(2), PrecisionMode::ToFuture)
                    .precise_time(&"2026-01-01 07:52:46[Europe/Oslo]".parse::<Zoned>()?)?
                    .unambiguous()?,
                "2026-01-01 08:00:00[Europe/Oslo]".parse::<Zoned>()?
            );
            Ok(())
        }

        #[test]
        fn rounding_on_dst_day() -> Result<(), Box<dyn Error>> {
            let precision = Precision::unchecked_new(Duration::from_mins(30), PrecisionMode::ToFuture);
            let ok_time = "2026-03-29 07:52:46[Europe/Oslo]".parse::<Zoned>()?;
            let gap_time = "2026-03-29 01:55:34[Europe/Oslo]".parse::<Zoned>()?;

            assert_eq!(
                precision.precise_time(&ok_time)?.unambiguous()?,
                "2026-03-29 08:00:00[Europe/Oslo]".parse::<Zoned>()?,
            );

            // since rounding 01:55:34 would end up at 02:00:00, which is when DST starts in this timezone,
            // trying to disambiguate the time using the reject strategy will return an error.
            assert!(precision.precise_time(&gap_time)?.unambiguous().is_err());

            // but if we really want a result, we can use the compatible strategy
            assert_eq!(
                precision.precise_time(&gap_time)?.compatible()?,
                // first time after DST time gap
                "2026-03-29 03:00:00[Europe/Oslo]".parse::<Zoned>()?,
            );

            Ok(())
        }

        #[test]
        fn already_rounded_wont_change() -> Result<(), Box<dyn Error>> {
            assert_eq!(
                Precision::unchecked_new(Duration::from_mins(5), PrecisionMode::ToFuture)
                    .precise_time(&"2026-01-01 08:45:00[Europe/Oslo]".parse::<Zoned>()?)?
                    .unambiguous()?,
                "2026-01-01 08:45:00[Europe/Oslo]".parse::<Zoned>()?,
            );
            Ok(())
        }
    }

    mod precise_time_with_base_time {
        use super::*;

        #[test]
        fn duration_wise_rounding_on_dst_day() -> Result<(), Box<dyn Error>> {
            let time = "2026-03-29 07:55:02[Europe/Oslo]".parse::<Zoned>()?;
            let base = time.start_of_day()?;

            assert_eq!(
                Precision::unchecked_new(Duration::from_hours(2), PrecisionMode::ToFuture)
                    .precise_time_with_base_time(&time, base.timestamp())?,
                "2026-03-29 09:00:00[Europe/Oslo]".parse::<Zoned>()?,
            );

            Ok(())
        }

        #[test]
        fn rounding_using_non_24h_divisor() -> Result<(), Box<dyn Error>> {
            let precision = Precision::new(Duration::from_mins(22), PrecisionMode::ToFuture)?;
            let time = "2026-01-02 07:55:02[Europe/Oslo]".parse::<Zoned>()?;
            let base = "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?;

            assert_eq!(
                precision.precise_time_with_base_time(&time, base.timestamp())?,
                "2026-01-02 08:16:00[Europe/Oslo]".parse::<Zoned>()?,
            );

            Ok(())
        }

        #[test]
        fn override_tz_base_before_transition_time_after_transition() -> Result<(), Box<dyn Error>> {
            // On DST day
            let time = "2026-03-29 07:55:02[Europe/Oslo]".parse::<Zoned>()?;
            let base = time.start_of_day()?;

            // Since the base is behind the DST transition and the time is after DST transition,
            // the times get converted into UTC but this DST transition will still "appear"
            // as a tangible hour.
            assert_eq!(
                Precision::unchecked_new(Duration::from_hours(2), PrecisionMode::ToFuture)
                    .precise_time_with_base_time(&time.with_time_zone(TimeZone::get("UTC")?), base.timestamp())?,
                "2026-03-29 07:00:00Z[UTC]".parse::<Zoned>()?, // = 09:00:00 in Europe/Oslo
            );

            Ok(())
        }

        #[test]
        fn override_tz_base_and_time_after_transition() -> Result<(), Box<dyn Error>> {
            // On DST day, but both after transition
            let time = "2026-03-29 07:55:02[Europe/Oslo]".parse::<Zoned>()?;
            let base = "2026-03-29 05:00:00[Europe/Oslo]".parse::<Zoned>()?;

            assert_eq!(
                Precision::unchecked_new(Duration::from_mins(30), PrecisionMode::ToFuture)
                    .precise_time_with_base_time(&time.with_time_zone(TimeZone::get("UTC")?), base.timestamp())?,
                "2026-03-29 06:00:00Z[UTC]".parse::<Zoned>()?, // = 08:00:00 in Europe/Oslo
            );

            Ok(())
        }
    }
}

mod running_result {
    use super::*;

    #[test]
    fn is_running() {
        assert!(RunningResult::<()>::Running(()).is_running());
        assert!(!RunningResult::<()>::Done(()).is_running());
    }

    #[test]
    fn is_done() {
        assert!(!RunningResult::<()>::Running(()).is_done());
        assert!(RunningResult::<()>::Done(()).is_done());
    }

    #[test]
    fn running_opt() {
        assert_eq!(RunningResult::<u8>::Running(10).running(), Some(10));
        assert_eq!(RunningResult::<u8>::Done(10).running(), None);
    }

    #[test]
    fn done_opt() {
        assert_eq!(RunningResult::<u8>::Running(10).done(), None);
        assert_eq!(RunningResult::<u8>::Done(10).done(), Some(10));
    }

    #[test]
    fn map_running() {
        assert_eq!(
            RunningResult::<u8>::Running(10).map_running(|x| x + 10),
            RunningResult::<u8>::Running(20)
        );
        assert_eq!(
            RunningResult::<u8>::Done(10).map_running(|x| x + 10),
            RunningResult::<u8>::Done(10),
        );
    }

    #[test]
    fn map_done() {
        assert_eq!(
            RunningResult::<u8>::Done(10).map_done(|x| x + 10),
            RunningResult::<u8>::Done(20)
        );
        assert_eq!(
            RunningResult::<u8>::Running(10).map_done(|x| x + 10),
            RunningResult::<u8>::Running(10),
        );
    }
}

mod complement_result {
    use super::*;

    #[test]
    fn is_single() {
        assert!(ComplementResult::<()>::Single(()).is_single());
        assert!(!ComplementResult::<()>::Split((), ()).is_single());
    }

    #[test]
    fn is_split() {
        assert!(!ComplementResult::<()>::Single(()).is_split());
        assert!(ComplementResult::<()>::Split((), ()).is_split());
    }

    #[test]
    fn single_opt() {
        assert_eq!(ComplementResult::<u8>::Single(10).single(), Some(10));
        assert_eq!(ComplementResult::<u8>::Split(10, 20).single(), None);
    }

    #[test]
    fn split_opt() {
        assert_eq!(ComplementResult::<u8>::Single(10).split(), None);
        assert_eq!(ComplementResult::<u8>::Split(10, 20).split(), Some((10, 20)));
    }

    #[test]
    fn map() {
        assert_eq!(
            ComplementResult::<u8>::Single(10).map(|x| x + 10),
            ComplementResult::<u8>::Single(20)
        );
        assert_eq!(
            ComplementResult::<u8>::Split(10, 20).map(|x| x + 10),
            ComplementResult::<u8>::Split(20, 30)
        );
    }
}

mod union_result {
    use super::*;

    #[test]
    fn is_united() {
        assert!(UnionResult::<()>::United(()).is_united());
        assert!(!UnionResult::<()>::Separate.is_united());
    }

    #[test]
    fn is_separate() {
        assert!(!UnionResult::<()>::United(()).is_separate());
        assert!(UnionResult::<()>::Separate.is_separate());
    }

    #[test]
    fn united_opt() {
        assert_eq!(UnionResult::<u8>::United(10).united(), Some(10));
        assert_eq!(UnionResult::<u8>::Separate.united(), None);
    }

    #[test]
    fn map_united() {
        assert_eq!(
            UnionResult::<u8>::United(10).map_united(|x| x + 10),
            UnionResult::United(20)
        );
        assert_eq!(
            UnionResult::<u8>::Separate.map_united(|x| x + 10),
            UnionResult::<u8>::Separate,
        );
    }
}

mod intersection_result {
    use super::*;

    #[test]
    fn is_intersected() {
        assert!(IntersectionResult::<()>::Intersected(()).is_intersected());
        assert!(!IntersectionResult::<()>::Separate.is_intersected());
    }

    #[test]
    fn is_separate() {
        assert!(!IntersectionResult::<()>::Intersected(()).is_separate());
        assert!(IntersectionResult::<()>::Separate.is_separate());
    }

    #[test]
    fn intersected_opt() {
        assert_eq!(IntersectionResult::<u8>::Intersected(10).intersected(), Some(10));
        assert_eq!(IntersectionResult::<u8>::Separate.intersected(), None);
    }

    #[test]
    fn map_intersected() {
        assert_eq!(
            IntersectionResult::<u8>::Intersected(10).map_intersected(|x| x + 10),
            IntersectionResult::<u8>::Intersected(20),
        );
        assert_eq!(
            IntersectionResult::<u8>::Separate.map_intersected(|x| x + 10),
            IntersectionResult::<u8>::Separate,
        );
    }
}

mod difference_result {
    use super::*;

    #[test]
    fn is_difference() {
        assert!(DifferenceResult::<()>::Single(()).is_difference());
        assert!(DifferenceResult::<()>::Split((), ()).is_difference());
        assert!(!DifferenceResult::<()>::Separate.is_difference());
    }

    #[test]
    fn is_shrunk() {
        assert!(DifferenceResult::<()>::Single(()).is_difference_single());
        assert!(!DifferenceResult::<()>::Split((), ()).is_difference_single());
        assert!(!DifferenceResult::<()>::Separate.is_difference_single());
    }

    #[test]
    fn is_split() {
        assert!(!DifferenceResult::<()>::Single(()).is_difference_split());
        assert!(DifferenceResult::<()>::Split((), ()).is_difference_split());
        assert!(!DifferenceResult::<()>::Separate.is_difference_split());
    }

    #[test]
    fn is_separate() {
        assert!(!DifferenceResult::<()>::Single(()).is_separate());
        assert!(!DifferenceResult::<()>::Split((), ()).is_separate());
        assert!(DifferenceResult::<()>::Separate.is_separate());
    }

    #[test]
    fn shrunk_opt() {
        assert_eq!(DifferenceResult::<u8>::Single(10).single(), Some(10));
        assert_eq!(DifferenceResult::<u8>::Split(10, 20).single(), None);
        assert_eq!(DifferenceResult::<u8>::Separate.single(), None);
    }

    #[test]
    fn split_opt() {
        assert_eq!(DifferenceResult::<u8>::Single(10).split(), None);
        assert_eq!(DifferenceResult::<u8>::Split(10, 20).split(), Some((10, 20)));
        assert_eq!(DifferenceResult::<u8>::Separate.split(), None);
    }

    #[test]
    fn map_difference() {
        assert_eq!(
            DifferenceResult::<u8>::Single(10).map_difference(|x| x + 10),
            DifferenceResult::<u8>::Single(20),
        );
        assert_eq!(
            DifferenceResult::<u8>::Split(10, 20).map_difference(|x| x + 10),
            DifferenceResult::<u8>::Split(20, 30),
        );
        assert_eq!(
            DifferenceResult::<u8>::Separate.map_difference(|x| x + 10),
            DifferenceResult::<u8>::Separate,
        );
    }
}

mod sym_difference_result {
    use super::*;

    #[test]
    fn has_symmetric_difference() {
        assert!(SymmetricDifferenceResult::<()>::Single(()).is_symmetric_difference());
        assert!(SymmetricDifferenceResult::<()>::Split((), ()).is_symmetric_difference());
        assert!(!SymmetricDifferenceResult::<()>::Separate.is_symmetric_difference());
    }

    #[test]
    fn is_shrunk() {
        assert!(SymmetricDifferenceResult::<()>::Single(()).is_single());
        assert!(!SymmetricDifferenceResult::<()>::Split((), ()).is_single());
        assert!(!SymmetricDifferenceResult::<()>::Separate.is_single());
    }

    #[test]
    fn is_split() {
        assert!(!SymmetricDifferenceResult::<()>::Single(()).is_split());
        assert!(SymmetricDifferenceResult::<()>::Split((), ()).is_split());
        assert!(!SymmetricDifferenceResult::<()>::Separate.is_split());
    }

    #[test]
    fn is_separate() {
        assert!(!SymmetricDifferenceResult::<()>::Single(()).is_separate());
        assert!(!SymmetricDifferenceResult::<()>::Split((), ()).is_separate());
        assert!(SymmetricDifferenceResult::<()>::Separate.is_separate());
    }

    #[test]
    fn shrunk_opt() {
        assert_eq!(SymmetricDifferenceResult::<u8>::Single(10).single(), Some(10));
        assert_eq!(SymmetricDifferenceResult::<u8>::Split(10, 20).single(), None);
        assert_eq!(SymmetricDifferenceResult::<u8>::Separate.single(), None);
    }

    #[test]
    fn split_opt() {
        assert_eq!(SymmetricDifferenceResult::<u8>::Single(10).split(), None);
        assert_eq!(SymmetricDifferenceResult::<u8>::Split(10, 20).split(), Some((10, 20)));
        assert_eq!(SymmetricDifferenceResult::<u8>::Separate.split(), None);
    }

    #[test]
    fn map_symmetric_difference() {
        assert_eq!(
            SymmetricDifferenceResult::<u8>::Single(10).map_symmetric_difference(|x| x + 10),
            SymmetricDifferenceResult::<u8>::Single(20),
        );
        assert_eq!(
            SymmetricDifferenceResult::<u8>::Split(10, 20).map_symmetric_difference(|x| x + 10),
            SymmetricDifferenceResult::<u8>::Split(20, 30),
        );
        assert_eq!(
            SymmetricDifferenceResult::<u8>::Separate.map_symmetric_difference(|x| x + 10),
            SymmetricDifferenceResult::<u8>::Separate,
        );
    }
}

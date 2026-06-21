//! Crate's testing utilities

#[cfg(test)]
use std::collections::HashMap;

#[cfg(test)]
use jiff::Timestamp;
use jiff::civil::{Date, date};
#[cfg(test)]
use jiff::civil::{Time, datetime};
#[cfg(test)]
use jiff::tz::TimeZone;

#[cfg(test)]
macro_rules! bin_op_map {
    ($($key:literal => $lhs_rhs_pair:expr),* $(,)?) => {
        ::std::collections::HashMap::from([
            $(
            (
                $key,
                crate::test_utils::BinOpPair::from($lhs_rhs_pair),
            ),
            )*
        ])
    };
}

#[cfg(test)]
pub(crate) use bin_op_map;

pub const FAKE_TODAY_DATE: Date = date(2026, 1, 1);

/// Returns the [`Timestamp`] of a date in UTC
///
/// # Panics
///
/// Panics if the call to [`date`] panicked or if the datetime couldn't be associated with the UTC timezone.
#[cfg(test)]
#[must_use]
pub fn date_timestamp(year: i16, month: i8, day: i8) -> Timestamp {
    date(year, month, day)
        .to_datetime(Time::midnight())
        .to_zoned(TimeZone::UTC)
        .unwrap()
        .timestamp()
}

/// Returns the [`Timestamp`] of a datetime in UTC
///
/// # Panics
///
/// Panics if the call to [`datetime`] panicked or if the datetime couldn't be associated with the UTC timezone.
#[cfg(test)]
#[must_use]
pub fn datetime_timestamp(year: i16, month: i8, day: i8, hour: i8, minute: i8, second: i8) -> Timestamp {
    datetime(year, month, day, hour, minute, second, 0)
        .to_zoned(TimeZone::UTC)
        .unwrap()
        .timestamp()
}

/// Returns the [`Timestamp`] of a datetime with nanoseconds in UTC
///
/// # Panics
///
/// Panics if the call to [`datetime`] panicked or if the datetime couldn't be associated with the UTC timezone.
#[cfg(test)]
#[must_use]
pub fn datetime_nanos_timestamp(
    year: i16,
    month: i8,
    day: i8,
    hour: i8,
    minute: i8,
    second: i8,
    nanos: i32,
) -> Timestamp {
    datetime(year, month, day, hour, minute, second, nanos)
        .to_zoned(TimeZone::UTC)
        .unwrap()
        .timestamp()
}

/// A test data map for a binary operation
#[cfg(test)]
pub type BinOpMap<Lhs, Rhs = Lhs> = HashMap<&'static str, BinOpPair<Lhs, Rhs>>;

/// A pair of types for a binary operation
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BinOpPair<Lhs, Rhs = Lhs> {
    lhs: Lhs,
    rhs: Rhs,
}

#[cfg(test)]
impl<Lhs, Rhs> BinOpPair<Lhs, Rhs> {
    #[must_use]
    pub fn new(lhs: Lhs, rhs: Rhs) -> Self {
        BinOpPair {
            lhs,
            rhs,
        }
    }

    #[must_use]
    pub fn lhs(&self) -> &Lhs {
        &self.lhs
    }

    #[must_use]
    pub fn rhs(&self) -> &Rhs {
        &self.rhs
    }

    #[must_use]
    pub fn take_lhs(self) -> Lhs {
        self.lhs
    }

    #[must_use]
    pub fn take_rhs(self) -> Rhs {
        self.rhs
    }
}

#[cfg(test)]
impl<Lhs, Rhs> From<(Lhs, Rhs)> for BinOpPair<Lhs, Rhs> {
    fn from((lhs, rhs): (Lhs, Rhs)) -> Self {
        Self::new(lhs, rhs)
    }
}

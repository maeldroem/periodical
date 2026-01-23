use chrono::NaiveTime;

/// Represents midnight as a [`NaiveTime`]
pub const NAIVE_TIME_MIDNIGHT: NaiveTime = NaiveTime::from_hms_opt(0, 0, 0)
    .expect("Provided valid hour/minute/second (hms) combination");

/// Represents noon as a [`NaiveTime`]
pub const NAIVE_TIME_NOON: NaiveTime = NaiveTime::from_hms_opt(12, 0, 0)
    .expect("Provided valid hour/minute/second (hms) combination");

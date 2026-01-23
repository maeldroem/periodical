use chrono::{DateTime, NaiveDate, TimeZone};

pub fn date<T: TimeZone>(tz: &T, year: i32, month: u32, day: u32) -> DateTime<T> {
    tz.from_local_datetime(&NaiveDate::from_ymd_opt(year, month, day).unwrap().into())
        .earliest()
        .unwrap()
}

pub fn datetime<T: TimeZone>(tz: &T, year: i32, month: u32, day: u32, hour: u32, min: u32, sec: u32) -> DateTime<T> {
    tz.from_local_datetime(
        &NaiveDate::from_ymd_opt(year, month, day)
            .unwrap()
            .and_hms_opt(hour, min, sec)
            .unwrap(),
    )
    .earliest()
    .unwrap()
}

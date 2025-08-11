#![no_main]

use chrono::{DateTime, Utc};
use libfuzzer_sys::fuzz_target;
use periodical::prelude::{AbsoluteBounds, ToAbsolute, ToRelative};

fuzz_target!(|data: (AbsoluteBounds, DateTime<Utc>)| {
    let (bounds, reference_time) = data;
    assert_eq!(bounds.to_relative(reference_time).to_absolute(reference_time), bounds)
});

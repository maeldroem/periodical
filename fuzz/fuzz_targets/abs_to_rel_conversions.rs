#![no_main]

use std::time::Duration;

use jiff::Timestamp;
use libfuzzer_sys::fuzz_target;
use periodical::prelude::{AbsoluteBoundPair, ToAbsolute, ToRelative};

fuzz_target!(|data: (AbsoluteBoundPair, Duration)| {
    let (bounds, reference_delta) = data;
    // Bypass lack of Arbitrary on Timestamp
    let reference = Timestamp::MIN
        .saturating_add(reference_delta)
        .expect("We are not using Span");
    assert_eq!(bounds.to_relative(reference).to_absolute(reference), bounds);
});

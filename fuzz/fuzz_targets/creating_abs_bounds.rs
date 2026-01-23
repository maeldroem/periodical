#![no_main]

use libfuzzer_sys::fuzz_target;
use periodical::intervals::absolute::{AbsoluteEndBound, AbsoluteStartBound};
use periodical::prelude::*;

fuzz_target!(|data: (AbsoluteStartBound, AbsoluteEndBound)| {
    let (start, end) = data;
    let _ = AbsoluteBounds::new(start, end);
});

#![no_main]

use libfuzzer_sys::fuzz_target;
use periodical::intervals::relative::{RelEndBound, RelStartBound};
use periodical::prelude::*;

fuzz_target!(|data: (RelStartBound, RelEndBound)| {
    let (start, end) = data;
    let _ = RelBoundPair::new(start, end);
});

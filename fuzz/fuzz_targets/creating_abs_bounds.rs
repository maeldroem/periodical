#![no_main]

use libfuzzer_sys::fuzz_target;
use periodical::intervals::absolute::{AbsEndBound, AbsStartBound};
use periodical::prelude::*;

fuzz_target!(|data: (AbsStartBound, AbsEndBound)| {
    let (start, end) = data;
    let _ = AbsBoundPair::new(start, end);
});

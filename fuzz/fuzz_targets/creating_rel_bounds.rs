#![no_main]

use libfuzzer_sys::fuzz_target;
use periodical::intervals::relative::{RelativeEndBound, RelativeStartBound};
use periodical::prelude::*;

fuzz_target!(|data: (RelativeStartBound, RelativeEndBound)| {
    let (start, end) = data;
    let _ = RelativeBounds::new(start, end);
});

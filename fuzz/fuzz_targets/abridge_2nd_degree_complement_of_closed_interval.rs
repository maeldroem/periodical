#![no_main]

use libfuzzer_sys::fuzz_target;
use periodical::prelude::*;

fuzz_target!(|closed_interval: ClosedAbsoluteInterval| {
    let (left_complement, right_complement) = closed_interval
        .complement()
        .split()
        .expect("The complement of a closed interval always results in a split complement");

    let left_2nd_degree_complement = left_complement
        .complement()
        .single()
        .expect("The complement of a half-open interval always results in a single complement");

    let right_2nd_degree_complement = right_complement
        .complement()
        .single()
        .expect("The complement of a half-open interval always results in a single complement");

    let abridgment_2nd_degree_complements = left_2nd_degree_complement.abridge(&right_2nd_degree_complement);

    assert_eq!(
        abridgment_2nd_degree_complements,
        AbsoluteInterval::from(closed_interval)
    );
});

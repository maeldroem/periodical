# Fuzzing

This uses the crate [`libfuzzer-sys`](https://lib.rs/libfuzzer-sys)
and the [`cargo-fuzz`](https://lib.rs/cargo-fuzz) Cargo plugin.

## Fuzzing policy

Fuzzing should only happen locally, ideally before releasing or when there is doubt on the stability of a function.

Only operations that have a stable _source of truth_ are fuzzed, otherwise manually creating unit test cases
is preferred.

A _source of truth_ is used in the context of when we are not only checking if an operation doesn't create a panic,
but also checking if the operation resulted in a correct output. The source of truth is the process through which
we can verify this correctness.

For example, there is no overlap fuzz target over any kind of interval, as the way to get the position of the overlap
is already what we are testing. Therefore, we must use a simpler source of truth, for example by creating a scenario
where we know there shouldn't be any overlap or there should be a full overlap.

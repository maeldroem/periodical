<!-- CLEAN THIS FILE AFTER CREATING PR -->

# Explanation

# Notes

<details>
<summary><h1>Changelog</h1></summary>

TODO: checks tests again after the refactoring
TODO: add missing conversions, rework conversions

## Added

- Created `IntervalType` and `IntervalTypeWithRel` to identify the different interval types
- Implemented `HasIntervalType` and `HasIntervalTypeWithRel` on every interval type to obtain their identifying type
- Created `test_data` module with test utilities
- Created test data for interval overlap and bound overlap
- Mock value behind `cfg!` in `time::date_today` for testing purposes

## Changed

- Completed tests/Fixed relevant tested code for…
  - `time`
  - `intervals`
    - `meta`
    - `absolute`
      - `bound`
      - `bound_pair`
      - `bounded_interval`
      - `emptiable_bound_pair`
      - `emptiable_interval`
      - `end_bound`
    - `relative`
      - `bound_pair`
      - `bounded_interval`
      - `emptiable_bound_pair`
      - `emptiable_interval`
      - `end_bound`
    - `ops`
      - `bound_cmp`
        - `bound_eq`
        - `bound_ord`
      - `abridge`
- Improved coverage xtask to allow for a test pattern to be provided, like with `cargo test`,
  in order to isolate some files that may be partially covered by other tests' actions

## Deprecated

-

## Removed

- Removed `PartialOrd` and `Ord` implementations on `*FiniteBoundPos`, as their previous implementation
  didn't conserve the `a == b => a.cmp(b) == Ordering::Equal` invariant.
- Removed re-exports of errors

## Fixed

-

## Security

-

</details>

<!-- CLEAN THIS FILE AFTER CREATING PR -->

# Explanation

# Notes

<details>
<summary><h1>Changelog</h1></summary>

## Added

- Created `IntervalType` and `IntervalTypeWithRel` to identify the different interval types
- Implemented `HasIntervalType` and `HasIntervalTypeWithRel` on every interval type to obtain their identifying type
- Added `HasIntervalType` and `HasIntervalTypeWithRel` to prelude
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
      - `finite_bound_position`
      - `finite_bound`
      - `finite_end_bound`
      - `finite_start_bound`
      - `half_bounded_interval`
      - `half_bounded_to_future_interval`
      - `half_bounded_to_past_interval`
      - `interval`
      - `start_bound`
    - `relative`
      - `bound_pair`
      - `bounded_interval`
      - `emptiable_bound_pair`
      - `emptiable_interval`
      - `end_bound`
      - `finite_bound`
      - `finite_end_bound`
      - `finite_start_bound`
      - `half_bounded_interval`
      - `half_bounded_to_future_interval`
      - `half_bounded_to_past_interval`
      - `interval`
      - `start_bound`
    - `ops`
      - `bound_cmp`
        - `bound_eq`
        - `bound_ord`
      - `precision`
        - `absolute`
          - `bound`
          - `interval`
        - `relative`
          - `bound`
          - `interval`
      - `abridge`
      - `extend`
- Improved coverage xtask to allow for a test pattern to be provided, like with `cargo test`,
  in order to isolate some files that may be partially covered by other tests' actions
- Slightly reformatted some code in `intervals::ops::abridge`
- Refactored `intervals::ops::extend`
- Reintegrated doc examples and code that was reliant on `intervals::ops::extend`

## Deprecated

-

## Removed

- Removed `PartialOrd` and `Ord` implementations on `*FiniteBoundPos`, as their previous implementation
  didn't conserve the `a == b => a.cmp(b) == Ordering::Equal` invariant.
- Removed re-exports of errors

## Fixed

- Fixed `intervals::ops::extend`'s doc examples

## Security

-

</details>

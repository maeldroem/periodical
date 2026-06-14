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

## Changed

- Completed/Fixed tests for…
  - `intervals`
    - `ops`
      - `bound_cmp`
        - `bound_eq`
      - `abridge`

## Deprecated

-

## Removed

- Removed `PartialOrd` and `Ord` implementations on `*FiniteBoundPos`, as their previous implementation
  didn't conserve the `a == b => a.cmp(b) == Ordering::Equal` invariant.

## Fixed

-

## Security

-

</details>

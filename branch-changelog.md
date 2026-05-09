<!-- CLEAN THIS FILE AFTER CREATING PR -->

# Explanation

Updated previous tests and created more tests for covering all the work so far.

# Notes

<details>
<summary><h1>Changelog</h1></summary>

## Added

- Tests to complete code coverage for `time`
- Tests to complete code coverage for `ops`
- Tests to complete code coverage for `intervals`
  - `bound_position`
  - `meta`
  - `special`
  - `absolute`
    - `bound`
    - `bound_pair`
    - `emptiable_bound_pair`
    - `end_bound`
    - `finite_bound`
    - `start_bound`
  - `relative`
    - `bound`
    - `bound_pair`
    - `emptiable_bound_pair`
    - `end_bound`
    - `finite_bound`
    - `start_bound`

## Changed

- `HasRelativity` now represents the relativity of the contained interval rather than the indicated relativity
  in the structure's name — Concerns `AbsoluteBoundPair`, `EmptiableAbsoluteBoundPair`, `RelativeBoundPair`,
  `EmptiableRelativeBoundPair`
- Converted conversions that use a boolean in a tuple to represent emptiness for an emptiable bound pair
  or emptiable interval to using `Option` to represent the empty variant

## Deprecated

-

## Removed

- Removed conversion from `(bool, bool)` to `Epsilon`, as `Epsilon` can be created from
  `(BoundInclusivity, BoundInclusivity)`, and `BoundInclusivity` can be created from a boolean
- (Internal) Removed `tests!` and `inline_docs!` macros

## Fixed

- Fixed wrong offset computation in `OffsetIsoWeek::from_date_with_offset`

## Security

-

</details>

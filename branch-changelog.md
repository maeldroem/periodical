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
    - `bounded_interval`
    - `emptiable_bound_pair`
    - `emptiable_interval`
    - `end_bound`
    - `finite_bound`
    - `half_bounded_interval`
    - `interval`
    - `start_bound`
  - `relative`
    - `bound`
    - `bound_pair`
    - `bounded_interval`
    - `emptiable_bound_pair`
    - `emptiable_interval`
    - `end_bound`
    - `finite_bound`
    - `half_bounded_interval`
    - `interval`
    - `start_bound`
- Implemented conversion from `EmptiableAbsoluteInterval` into `HalfBoundedAbsoluteInterval`
- Implemented conversion from `EmptiableRelativeInterval` into `HalfBoundedRelativeInterval`
- Created a list of bound pair pairs for test cases involving operations (subject, compared)
- Added missing implementation of `Abridgable` for `EmptiableRelativeInterval`

## Changed

- `HasRelativity` now represents the relativity of the contained interval rather than the indicated relativity
  in the structure's name — Concerns `AbsoluteBoundPair`, `EmptiableAbsoluteBoundPair`, `RelativeBoundPair`,
  `EmptiableRelativeBoundPair`
- Converted conversions that use a boolean in a tuple to represent emptiness for an emptiable bound pair
  or emptiable interval to using `Option` to represent the empty variant
- Changed conversion of `((Timestamp/SignedDuration, BoundInclusivity), OpeningDirection)` for half bounded intervals
  to `(Timestamp/SignedDuration, BoundInclusivity, OpeningDirection)`.

## Deprecated

-

## Removed

- Removed conversion from `(bool, bool)` to `Epsilon`, as `Epsilon` can be created from
  `(BoundInclusivity, BoundInclusivity)`, and `BoundInclusivity` can be created from a boolean
- Removed conversion from types that are already handled by `AbsoluteBoundPair` on `AbsoluteInterval`
- Removed conversion from types that are already handled by `RelativeBoundPair` on `RelativeInterval`
- Removed conversion from types that are already handled by `EmptiableAbsoluteBoundPair` on `EmptiableAbsoluteInterval`
- Removed conversion from types that are already handled by `EmptiableRelativeBoundPair` on `EmptiableRelativeInterval`
- (Internal) Removed `tests!` and `inline_docs!` macros

## Fixed

- Fixed wrong offset computation in `OffsetIsoWeek::from_date_with_offset`
- Fixed panic due to usage of `SignedDuration::from_nanos_i128` instead of `SignedDuration::try_from_nanos_i128` in
  `BoundedRelativeInterval::new_with_length`
- Fixed panic due to usage of `SignedDuration::from_nanos_i128` instead of `SignedDuration::try_from_nanos_i128` in
  `BoundedRelativeInterval::new_with_length_and_inclusivity`

## Security

-

</details>

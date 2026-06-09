<!-- CLEAN THIS FILE AFTER CREATING PR -->

# Explanation

Updated previous tests and created more tests for covering all the work so far.

For allowing more granular control over interval bounds, we need a way to represent start/end bounds that are
finite only.
This allows for type safety when comparing finite bounds and not having to use their possibly infinite variants
to perform comparisons that then have to be unwrapped into finite variants.

Reworked multiple structures to guarantee more invariants.

# Notes

<details>
<summary><h1>Changelog</h1></summary>

## Added

TODO: checks tests again after the refactoring
TODO: add missing conversions, rework conversions
TODO: once all done, PR onto dev to sync, then continue unit tests

- Checked, fixed, and completed documentation for…
  - `intervals`
    - `absolute`
      - `bound_pair`
      - `bound`
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
      - `bound`
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
    - `convenience`
      - `absolute`
        - `bounded_interval`
        - `half_bounded_interval`
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
      - `set_ops`
        - `diff`
        - `intersect`
        - `sym_diff`
      - `abridge`
- Implemented conversion from `EmptiableAbsInterval` into `HalfBoundedAbsInterval`
- Implemented conversion from `EmptiableRelInterval` into `HalfBoundedRelInterval`
- Created a list of bound pair pairs for test cases involving operations (subject, compared)
- Added missing implementation of `Abridgable` for `EmptiableRelInterval`
- Adopted policy of binary operations returning the strictest possible type, "strictest binary operation output policy"
- Adopted policy of no generic implementations for binary operations, "no binary operation generic impl policy"
- Adopted "no binary operation over-compatibility impl policy"
- Added missing conversion from finite bounds for bounded and half-bounded intervals
- Added `BoundExtremality` to represent bound extremality
- Added and implemented on relevant types `HasBoundExtremality` to return a bound's extremality
- Added conversions from `(*FiniteBound, BoundExtremality)` to `*Bound`
- Added `HasBoundExtremality` to prelude
- Added finite variants for start/end bounds
- Added finite variant for `*Bound`
- Added bound variants for cmp traits (`PartialEq`, `Eq`, `PartialOrd`, `Ord`) in order to compare bounds
  semantically rather than syntactically
- Added `bound_max` and `bound_min` functions to complete bound comparison toolbox
- Added length-related creation methods on absolute and relative bounded intervals
- Added `set_length_from_start` and `set_length_from_end` on absolute bounded intervals
- Added `swap_reference_and_compared` on `BoundOverlapAmbiguity`

## Changed

- `HasRelativity` now represents the relativity of the contained interval rather than the indicated relativity
  in the structure's name — Concerns `AbsBoundPair`, `EmptiableAbsBoundPair`, `RelBoundPair`,
  `EmptiableRelBoundPair`
- Converted conversions that use a boolean in a tuple to represent emptiness for an emptiable bound pair
  or emptiable interval to using `Option` to represent the empty variant
- Changed conversion of `((Timestamp/SignedDuration, BoundInclusivity), OpeningDirection)` for half bounded intervals
  to `(Timestamp/SignedDuration, BoundInclusivity, OpeningDirection)`
- Adapted binary operation implementations to respect adopted policies regarding binary operations
  - `Abridgable`
  - `Extensible` (WIP)
- Renamed `*FiniteBound` to `*FiniteBoundPosition` for clarity
- `*StartBound` and `*EndBound` now contain a `*FiniteStartBound`/`*FiniteEndBound` in their `Finite` variant
- Refactored comparisons between bounds through the use of dedicated bound comparison traits
- Changed internal structure of bounded intervals to use start/end finite bounds
- Changed internal structure of half-bounded intervals to use a finite bound position
- Renamed `Absolute`/`Relative` by `Abs`/`Rel` to reduce space taken
- Renamed `*FiniteBoundPosition` to `*FiniteBoundPos` to reduce space taken
- Renamed `new_with_inclusivity` on `*FiniteBoundPos` to `new_with_incl` to reduce space taken
- Renamed `Differentiable`'s methods to reduce space taken
- Renamed `SymmetricallyDifferentiable`'s methods to reduce space taken
- Renamed `BoundContainmentPosition` to `BoundContainmentPos` to reduce space taken
- Renamed `DisambiguatedBoundContainmentPosition` to `DisambiguatedBoundContainmentPos` to reduce space taken

## Deprecated

-

## Removed

- Removed conversion from `(bool, bool)` to `Epsilon`, as `Epsilon` can be created from
  `(BoundInclusivity, BoundInclusivity)`, and `BoundInclusivity` can be created from a boolean
- Removed conversion from types that are already handled by `AbsBoundPair` on `AbsInterval`
- Removed conversion from types that are already handled by `RelBoundPair` on `RelInterval`
- Removed conversion from types that are already handled by `EmptiableAbsBoundPair` on `EmptiableAbsInterval`
- Removed conversion from types that are already handled by `EmptiableRelBoundPair` on `EmptiableRelInterval`
- (Internal) Removed `tests!` and `inline_docs!` macros

## Fixed

- Fixed wrong offset computation in `OffsetIsoWeek::from_date_with_offset`
- Fixed panic due to usage of `SignedDuration::from_nanos_i128` instead of `SignedDuration::try_from_nanos_i128` in
  `BoundedRelInterval::new_with_length`
- Fixed panic due to usage of `SignedDuration::from_nanos_i128` instead of `SignedDuration::try_from_nanos_i128` in
  `BoundedRelInterval::new_with_length_and_inclusivity`

## Security

-

</details>

<!-- CLEAN THIS FILE AFTER CREATING PR -->

# Explanation

Implemented a ton of conversion methods for intervals and converted single-variant enum errors
to tag struct errors.

# Notes

Find way to handle multiple interval durations to handle correctly mathematical operations
(addition, subtraction, etc.)

Remove implementations of operations where it always returns an error

<details>
<summary><h1>Changelog</h1></summary>

## Added

- Added methods to retrieve individual variants of `AbsoluteInterval` (`bounded`, `half_bounded`, `unbounded`)
- Implemented `From<BoundedAbsoluteInterval>` on `AbsoluteBoundPair`
- Implemented `From<HalfBoundedAbsoluteInterval>` on `AbsoluteBoundPair`
- Implemented `From<AbsoluteInterval>` on `AbsoluteBoundPair`
- Implemented `From<UnboundedInterval>` on `AbsoluteBoundPair`
- Implemented `From<BoundedAbsoluteInterval>` on `EmptiableAbsoluteBoundPair`
- Implemented `From<HalfBoundedAbsoluteInterval>` on `EmptiableAbsoluteBoundPair`
- Implemented `From<AbsoluteInterval>` on `EmptiableAbsoluteBoundPair`
- Implemented `From<EmptiableAbsoluteInterval>` on `EmptiableAbsoluteBoundPair`
- Implemented `From<UnboundedInterval>` on `EmptiableAbsoluteBoundPair`
- Implemented `From<EmptyInterval>` on `EmptiableAbsoluteBoundPair`
- Implemented `TryFrom<AbsoluteBound>` on `AbsoluteStartBound`
- Implemented `TryFrom<AbsoluteBound>` on `AbsoluteEndBound`
- Implemented `TryFrom<EmptiableAbsoluteBoundPair>` on `BoundedAbsoluteInterval`
- Implemented `TryFrom<EmptiableAbsoluteInterval>` on `BoundedAbsoluteInterval`
- Implemented `TryFrom<EmptiableAbsoluteInterval>` on `AbsoluteBoundPair`

- Added methods to retrieve individual variants of `RelativeInterval` (`bounded`, `half_bounded`, `unbounded`)
- Implemented `From<BoundedRelativeInterval>` on `RelativeBoundPair`
- Implemented `From<HalfBoundedRelativeInterval>` on `RelativeBoundPair`
- Implemented `From<RelativeInterval>` on `RelativeBoundPair`
- Implemented `From<UnboundedInterval>` on `RelativeBoundPair`
- Implemented `From<BoundedRelativeInterval>` on `EmptiableRelativeBoundPair`
- Implemented `From<HalfBoundedRelativeInterval>` on `EmptiableRelativeBoundPair`
- Implemented `From<RelativeInterval>` on `EmptiableRelativeBoundPair`
- Implemented `From<EmptiableRelativeInterval>` on `EmptiableRelativeBoundPair`
- Implemented `From<UnboundedInterval>` on `EmptiableRelativeBoundPair`
- Implemented `From<EmptyInterval>` on `EmptiableRelativeBoundPair`
- Implemented `TryFrom<RelativeBound>` on `RelativeStartBound`
- Implemented `TryFrom<RelativeBound>` on `RelativeEndBound`
- Implemented `TryFrom<EmptiableRelativeBoundPair>` on `BoundedRelativeInterval`
- Implemented `TryFrom<EmptiableRelativeInterval>` on `BoundedRelativeInterval`
- Implemented `TryFrom<EmptiableRelativeInterval>` on `RelativeBoundPair`

- Added methods to convert `UnboundedInterval` into either `AbsoluteBoundPair`, `EmptiableAbsoluteBoundPair`,
  `AbsoluteInterval`, `EmptiableAbsoluteInterval`
- Added methods to convert `UnboundedInterval` into either `RelativeBoundPair`, `EmptiableRelativeBoundPair`,
  `RelativeInterval`, `EmptiableRelativeInterval`
- Implemented `TryFrom<AbsoluteBoundPair>` on `UnboundedInterval`
- Implemented `TryFrom<EmptiableAbsoluteBoundPair>` on `UnboundedInterval`
- Implemented `TryFrom<AbsoluteInterval>` on `UnboundedInterval`
- Implemented `TryFrom<EmptiableAbsoluteInterval>` on `UnboundedInterval`
- Implemented `TryFrom<RelativeBoundPair>` on `UnboundedInterval`
- Implemented `TryFrom<EmptiableRelativeBoundPair>` on `UnboundedInterval`
- Implemented `TryFrom<RelativeInterval>` on `UnboundedInterval`
- Implemented `TryFrom<EmptiableRelativeInterval>` on `UnboundedInterval`

- Added methods to convert `EmptyInterval` into either `EmptiableAbsoluteBoundPair` or `EmptiableAbsoluteInterval`
- Added methods to convert `EmptyInterval` into either `EmptiableRelativeBoundPair` or `EmptiableRelativeInterval`
- Implemented `TryFrom<EmptiableAbsoluteBoundPair>` on `EmptyInterval`
- Implemented `TryFrom<EmptiableAbsoluteInterval>` on `EmptyInterval`
- Implemented `TryFrom<EmptiableRelativeBoundPair>` on `EmptyInterval`
- Implemented `TryFrom<EmptiableRelativeInterval>` on `EmptyInterval`

- Implemented `to_range_bound_with` on `BoundInclusivity`

## Changed

- `BoundedAbsoluteIntervalFromAbsoluteIntervalError` was converted from a single-variant enum to a tag struct
  and renamed to `BoundedAbsoluteIntervalTryFromAbsoluteIntervalError`
- `AbsoluteBoundPairFromEmptiableAbsoluteBoundPairError` was converted from a single-variant enum to a tag struct
  and renamed to `AbsoluteBoundPairTryFromEmptiableAbsoluteBoundPairError`
- `BoundedAbsoluteIntervalFromAbsoluteBoundPairError` was converted from a single-variant enum to a tag struct
  and renamed to `BoundedAbsoluteIntervalTryFromAbsoluteBoundPairError`
- `AbsoluteFiniteBoundFromBoundError` was converted from a single-variant enum to a tag struct
  and renamed to `AbsoluteFiniteBoundTryFromBoundError`
- `HalfBoundedAbsoluteIntervalFromAbsoluteBoundPairError` was converted from a single-variant enum to a tag struct
  and renamed to `HalfBoundedAbsoluteIntervalTryFromAbsoluteBoundPairError`
- `HalfBoundedAbsoluteIntervalFromAbsoluteIntervalError` was converted from a single-variant enum to a tag struct
  and renamed `HalfBoundedAbsoluteIntervalTryFromAbsoluteIntervalError`
- `TryFrom<AbsoluteInterval>` implementation on `BoundedAbsoluteInterval` was re-expressed using the new
  variant retrieval methods of `AbsoluteInterval`
- `BoundedAbsoluteInterval::to_emptiable` was renamed `to_emptiable_interval` for explicitness
- `HalfBoundedAbsoluteInterval::to_emptiable` was renamed `to_emptiable_interval` for explicitness

- `BoundedRelativeIntervalFromRelativeIntervalError` was converted from a single-variant enum to a tag struct
  and renamed to `BoundedRelativeIntervalTryFromRelativeIntervalError`
- `RelativeBoundPairFromEmptiableRelativeBoundPairError` was converted from a single-variant enum to a tag struct
  and renamed to `RelativeBoundPairTryFromEmptiableRelativeBoundPairError`
- `BoundedRelativeIntervalFromRelativeBoundPairError` was converted from a single-variant enum to a tag struct
  and renamed to `BoundedRelativeIntervalTryFromRelativeBoundPairError`
- `RelativeFiniteBoundFromBoundError` was converted from a single-variant enum to a tag struct
  and renamed to `RelativeFiniteBoundTryFromBoundError`
- `HalfBoundedRelativeIntervalFromRelativeBoundPairError` was converted from a single-variant enum to a tag struct
  and renamed to `HalfBoundedRelativeIntervalTryFromRelativeBoundPairError`
- `HalfBoundedRelativeIntervalFromRelativeIntervalError` was converted from a single-variant enum to a tag struct
  and renamed to `HalfBoundedRelativeIntervalTryFromRelativeIntervalError`
- `TryFrom<RelativeInterval>` implementation on `BoundedRelativeInterval` was re-expressed using the new
  variant retrieval methods of `RelativeInterval`
- `BoundedRelativeInterval::to_emptiable` was renamed `to_emptiable_interval` for explicitness
- `HalfBoundedRelativeInterval::to_emptiable` was renamed `to_emptiable_interval` for explicitness
- Renamed `Emptiable` trait to `IsEmpty` for explicitness

- `OverlapRemovalErr` was converted from a single-variant enum to a tag struct and renamed
  to `OverlapRemovalNoOverlapFoundError`
- `GapFillError` was converted from a single-variant enum to a tag struct and renamed
  to `GapFillOverlapFoundError`
- `PrecisionCreationError` was converted from a single-variant enum to a tag struct and renamed
  to `PrecisionCreationPrecisionIsZeroError`
- `PrecisionError` was converted from a single-variant enum to a tag struct
  and renamed to `PrecisionOutOfRangeDateError`
- `EpsilonInterpretationDurationError` was converted from a single-variant enum to a tag struct
  and renamed to `EpsilonInterpretationDurationOverflowError`

## Deprecated

- Things you've marked as deprecated

## Removed

- Removed `UnboundedIntervalConversionErr` to instead use specific conversion error types

</details>

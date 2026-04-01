<!-- CLEAN THIS FILE AFTER CREATING PR -->

# Notes

Find way to handle multiple interval durations to handle correctly mathematical operations
(addition, subtraction, etc.)

FIXME: Conversion errors and descriptions are backwards

FIXME: Remove single-variant errors

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
- `AbsoluteBoundPairFromEmptiableAbsoluteBoundPairError` was converted from a single-variant enum to a tag struct
- `TryFrom<AbsoluteInterval>` implementation on `BoundedAbsoluteInterval` was re-expressed using the new
  variant retrieval methods of `AbsoluteInterval`
- `BoundedAbsoluteInterval::to_emptiable` was renamed `to_emptiable_interval` for explicitness
- `HalfBoundedAbsoluteInterval::to_emptiable` was renamed `to_emptiable_interval` for explicitness
- `BoundedRelativeIntervalFromRelativeIntervalError` was converted from a single-variant enum to a tag struct
- `RelativeBoundPairFromEmptiableRelativeBoundPairError` was converted from a single-variant enum to a tag struct
- `TryFrom<RelativeInterval>` implementation on `BoundedRelativeInterval` was re-expressed using the new
  variant retrieval methods of `RelativeInterval`
- `BoundedRelativeInterval::to_emptiable` was renamed `to_emptiable_interval` for explicitness
- `HalfBoundedRelativeInterval::to_emptiable` was renamed `to_emptiable_interval` for explicitness
- Renamed `Emptiable` trait to `IsEmpty` for explicitness

## Deprecated

- Things you've marked as deprecated

## Removed

- Removed `UnboundedIntervalConversionErr` to instead use specific conversion error types

## Fixed

- Things you've fixed

## Security

- Vulnerabilities you've fixed (add relevant CVE and any other relevant info/links)

</details>

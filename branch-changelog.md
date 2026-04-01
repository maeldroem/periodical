<!-- CLEAN THIS FILE AFTER CREATING PR -->

# Notes

Find way to handle multiple interval durations to handle correctly mathematical operations
(addition, subtraction, etc.)

<details>
<summary><h1>Changelog</h1></summary>

## Added

- Added methods to retrieve individual variants of `AbsoluteInterval` (`bounded`, `half_bounded`, `unbounded`)
- Added methods to retrieve individual variants of `RelativeInterval` (`bounded`, `half_bounded`, `unbounded`)
- Implemented `TryFrom<AbsoluteBound>` on `AbsoluteStartBound`
- Implemented `TryFrom<AbsoluteBound>` on `AbsoluteEndBound`
- Implemented `TryFrom<EmptiableAbsoluteBoundPair>` on `BoundedAbsoluteInterval`
- Implemented `TryFrom<EmptiableAbsoluteInterval>` on `BoundedAbsoluteInterval`
- Implemented `TryFrom<RelativeBound>` on `RelativeStartBound`
- Implemented `TryFrom<RelativeBound>` on `RelativeEndBound`
- Implemented `TryFrom<EmptiableRelativeBoundPair>` on `BoundedRelativeInterval`
- Implemented `TryFrom<EmptiableRelativeInterval>` on `BoundedRelativeInterval`
- Implemented `to_range_bound_with` on `BoundInclusivity`

## Changed

- `BoundedAbsoluteIntervalFromAbsoluteIntervalError` was converted from a single-variant enum to a tag struct
- `TryFrom<AbsoluteInterval>` implementation on `BoundedAbsoluteInterval` was re-expressed using the new
  variant retrieval methods of `AbsoluteInterval`
- `BoundedAbsoluteInterval::to_emptiable` was renamed `to_emptiable_interval` for explicitness
- `HalfBoundedAbsoluteInterval::to_emptiable` was renamed `to_emptiable_interval` for explicitness
- `BoundedAbsoluteIntervalFromRelativeIntervalError` was converted from a single-variant enum to a tag struct
- `TryFrom<RelativeInterval>` implementation on `BoundedRelativeInterval` was re-expressed using the new
  variant retrieval methods of `RelativeInterval`
- `BoundedRelativeInterval::to_emptiable` was renamed `to_emptiable_interval` for explicitness
- `HalfBoundedRelativeInterval::to_emptiable` was renamed `to_emptiable_interval` for explicitness
- Renamed `Emptiable` trait to `IsEmpty` for explicitness

## Deprecated

- Things you've marked as deprecated

## Removed

- Things you've removed

## Fixed

- Things you've fixed

## Security

- Vulnerabilities you've fixed (add relevant CVE and any other relevant info/links)

</details>

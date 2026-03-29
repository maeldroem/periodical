<!-- CLEAN THIS FILE AFTER CREATING PR -->

# Changelog

## Added

- [ ] Implement `Emptiable` on every interval type
- [x] Implement additional conversions on absolute emptiable types
- [x] Implement additional conversions on relative emptiable types

## Changed

- [x] Renamed `AbsoluteInterval::to_emptiable_interval` to `to_emptiable`
- [x] Renamed `RelativeInterval::to_emptiable_interval` to `to_emptiable`
- [x] `EmptiableAbsoluteInterval` has the same semantics as `EmptiableAbsoluteBoundPair`:
      two variants: `Bound`, `Empty`.
- [x] `EmptiableRelativeInterval` has the same semantics as `EmptiableRelativeBoundPair`:
      two variants: `Bound`, `Empty`.

## Deprecated

- Things you've marked as deprecated

## Removed

- Things you've removed

## Fixed

- Things you've fixed

## Security

- Vulnerabilities you've fixed (add relevant CVE and any other relevant info/links)

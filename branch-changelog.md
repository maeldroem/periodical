<!-- CLEAN THIS FILE AFTER CREATING PR -->

# Explanation

Link relevant issues and PRs here!

Explain the motivation for this PR and what it does/solves

<details>
<summary><h1>Changelog</h1></summary>

Remove the sections that don't apply to your PR

## Added

- Added `to_interval` on `AbsoluteBoundPair`
- Added `to_emptiable_interval` on `AbsoluteBoundPair`
- Added `to_emptiable_interval` on `EmptiableAbsoluteBoundPair`

- Added `to_interval` on `RelativeBoundPair`
- Added `to_emptiable_interval` on `RelativeBoundPair`
- Added `to_emptiable_interval` on `EmptiableRelativeBoundPair`

## Changed

- Changed all usages of `AbsoluteStartBound::Finite(x)` to `x.to_start_bound()`
- Changed all usages of `AbsoluteEndBound::Finite(x)` to `x.to_end_bound()`
- Changed all usages of `AbsoluteBound::Start(x)` to `x.to_bound()`
- Changed all usages of `AbsoluteBound::End(x)` to `x.to_bound()`
- Changed all usages of `AbsoluteInterval::from(x)` to `x.to_interval()`
- Changed all usages of `EmptiableAbsoluteInterval::from(x)` to `x.to_emptiable_interval()`

- Changed all usages of `RelativeStartBound::Finite(x)` to `x.to_start_bound()`
- Changed all usages of `RelativeEndBound::Finite(x)` to `x.to_end_bound()`
- Changed all usages of `RelativeBound::Start(x)` to `x.to_bound()`
- Changed all usages of `RelativeBound::End(x)` to `x.to_bound()`
- Changed all usages of `RelativeInterval::from(x)` to `x.to_interval()`
- Changed all usages of `EmptiableRelativeInterval::from(x)` to `x.to_emptiable_interval()`

## Deprecated

- Things you've marked as deprecated

## Removed

- Things you've removed

## Fixed

- Things you've fixed

## Security

- Vulnerabilities you've fixed (add relevant CVE and any other relevant info/links)

</details>

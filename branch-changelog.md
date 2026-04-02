<!-- CLEAN THIS FILE AFTER CREATING PR -->

# Explanation

Link relevant issues and PRs here!

Explain the motivation for this PR and what it does/solves

<details>
<summary><h1>Changelog</h1></summary>

## Added

- Prepared `intervals::ops::precision` for relative precision change (`precision::relative::bound`, `precision::relative::interval`)

## Changed

- Split `intervals::ops::precision` into `precision::absolute::bound` and `precision::absolute::interval`
- Split `intervals::ops::set_ops` into `set_ops::diff`, `set_ops::intersect`, `set_ops::sym_diff`,
  and `set_ops::unite`
- Split `iter::intervals::layered_bounds` into `layered_bounds::state`, `layered_bounds::abs_state_change`,
  `layered_bounds::rel_state_change`, `layered_bounds::absolute`, and `layered_bounds::relative`

## Deprecated

- Things you've marked as deprecated

## Removed

- Things you've removed

## Fixed

-

## Security

- Vulnerabilities you've fixed (add relevant CVE and any other relevant info/links)

</details>

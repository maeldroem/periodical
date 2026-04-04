<!-- CLEAN THIS FILE AFTER CREATING PR -->

# Explanation

Link relevant issues and PRs here!

Explain the motivation for this PR and what it does/solves

# Notes

Where should the actual logic for conversion be located? Either within the item's `impl`
or the relevant `From`/`TryFrom` impl? I believe that, where possible, logic should be implemented
in the item's `impl` under an explicit name, which is later used in the `From`/`TryFrom` impl.

<details>
<summary><h1>Changelog</h1></summary>

## Added

- Implemented `unchecked_new_with_offset` on `OffsetIsoWeek`
- Implemented `from_date_with_offset` and `from_date` on `OffsetIsoWeek`
- Added `Computation` variant to `OffsetIsoWeekCreationError`
- Implemented `zero_based_nth_day` and `one_based_nth_day` on `OffsetIsoWeek`

## Changed

-

## Deprecated

-

## Removed

-

## Fixed

-

## Security

-

</details>

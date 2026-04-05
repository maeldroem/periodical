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
- Implemented `start_weekday` and `end_weekday` on `OffsetIsoWeek`
- Implemented `weekday_date` on `OffsetIsoWeek`
- Implemented `TryFrom<Date>` and `TryFrom<(Date, i8)>` on `OffsetIsoWeek`
- Implemented `offset_week_after_duration_from_date`, `offset_week_before_duration_from_date`,
  `week_after_duration_from_date`, and `week_before_duration_from_date` on `OffsetIsoWeek`
- Implemented `offset_week_after_duration_from_today`, `week_after_duration_from_today`,
  `offset_week_before_duration_from_today`, and `week_before_duration_from_today` on `OffsetIsoWeek`
- Implemented `this_week`, `this_offset_week`, `next_week`, `next_offset_week`, `previous_week`,
  and `previous_offset_week` on `OffsetIsoWeek`

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

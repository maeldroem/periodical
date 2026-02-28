<!-- DELETE THIS FILE BEFORE CREATING PR -->

# Personal notes

- Check logic of absolute.rs and relative.rs to avoid confusion, especially since
  relative.rs has bounds that can be defined as two offsets OR one offset and a length
- Renamed from/to times to start/end

# Changelog

## Added

- [x] Added `NaiveWeek` in `time`
- [x] Added `NaiveWeekInYear` in `time`
- [x] Added `Month` in `time`
- [x] Added `NaiveMonthInYear` in `time`
- [x] Added method to compute the number of weeks in a given year with a custom week start day
- [x] Added `checked_add_calendar_week_offset_to_date` and its subtraction variant
- [x] Added `checked_add_calendar_anchor_offset_to_date` and its subtraction variant

## Changed

- [ ] Migrating `intervals::absolute` to jiff
- [ ] Migrating `intervals::relative` to jiff
- [ ] Migrating `intervals::special` to jiff
- [x] Migrating `time` to jiff
- [ ] Migrating `intervals::ops` to jiff

- [ ] Migrating `intervals::absolute`'s tests to jiff
- [ ] Migrating `intervals::relative`'s tests to jiff
- [ ] Migrating `intervals::special`'s tests to jiff
- [ ] Migrating `time`'s tests to jiff
- [ ] Migrating `intervals::ops`'s tests to jiff

- [ ] Migrating `intervals::absolute`'s examples to jiff
- [ ] Migrating `intervals::relative`'s examples to jiff
- [ ] Migrating `intervals::special`'s examples to jiff
- [ ] Migrating `intervals::ops`'s examples to jiff

- [ ] Updating `time` tests to check new structures
- [ ] Finishing `time` docs

- [ ] Renamed all occurrences of "from" and "to" to "start" and "end" respectively to avoid confusion
  and to make it easier to refer to ("start time" is more explicit than "from time")

- [x] Renamed `NaiveDuration` to `CalendarAnchorOffset`

## Deprecated

## Removed

## Fixed

## Security

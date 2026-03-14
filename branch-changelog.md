<!-- DELETE THIS FILE BEFORE CREATING PR -->

# Personal notes

- Check logic of absolute.rs and relative.rs to avoid confusion, especially since
  relative.rs has bounds that can be defined as two offsets OR one offset and a length
- Rename from/to times to start/end
- Rename "bounds" (plural) to bound pair
- Create migration guide/notes from 0.2 to 0.3

# Changelog

## Added

- [x] Added `OffsetIsoWeek` in `time`
- [x] Added `Month` in `time`
- [x] Added `NaiveMonthInYear` in `time`
- [x] Added `checked_add_calendar_week_offset_to_date` and its subtraction variant
- [x] Added `checked_add_calendar_anchor_offset_to_date` and its subtraction variant
- [x] Added `iso_weeks_in_year` to return the number of ISO weeks in a given year
- [x] Added `PrecisionMode`
- [x] Added a way to precise signed and unsigned durations (`Precision::precise_duration`
  `Precision::precise_signed_duration`)
- [x] Added a way to precise signed and unsigned amounts of nanoseconds (`Precision::precise_unsigned_nanos`,
  `Precision::precise_signed_nanos`)
- [x] Added convenience method `.to_start_bound()` to get an `AbsoluteStartBound` from an `AbsoluteFiniteBound`
- [x] Added convenience method `.to_end_bound()` to get an `AbsoluteEndBound` from an `AbsoluteFiniteBound`
- [ ] Added convenience method `.to_start_bound()` to get a `RelativeStartBound` from a `RelativeFiniteBound`
- [ ] Added convenience method `.to_end_bound()` to get a `RelativeEndBound` from a `RelativeFiniteBound`

## Changed

- [x] Migrated `intervals::absolute` to jiff
  - [ ] Migrated `bound_pair` to jiff
  - [ ] Migrated `bound` to jiff
  - [ ] Migrated `bounded_interval` to jiff
  - [ ] Migrated `emptiable_bound_pair` to jiff
  - [x] Migrated `end_bound` to jiff
  - [x] Migrated `finite_bound` to jiff
  - [ ] Migrated `half_bounded_interval` to jiff
  - [ ] Migrated `interval` to jiff
  - [x] Migrated `start_bound` to jiff
- [ ] Migrated `intervals::relative` to jiff
  - [ ] Migrated `bound_pair` to jiff
  - [ ] Migrated `bound` to jiff
  - [ ] Migrated `bounded_interval` to jiff
  - [ ] Migrated `emptiable_bound_pair` to jiff
  - [ ] Migrated `end_bound` to jiff
  - [ ] Migrated `finite_bound` to jiff
  - [ ] Migrated `half_bounded_interval` to jiff
  - [ ] Migrated `interval` to jiff
  - [ ] Migrated `start_bound` to jiff
- [ ] Migrated `convenience::absolute` to jiff
- [ ] Migrated `convenience::relative` to jiff
- [x] Migrated `intervals::special` to jiff
- [x] Migrated `time` to jiff
- [x] Migrated `ops` to jiff

- [ ] Migrated `intervals::absolute`'s tests to jiff
  - [ ] Migrated `bound_pair`'s tests to jiff
  - [ ] Migrated `bound`'s tests to jiff
  - [ ] Migrated `bounded_interval`'s tests to jiff
  - [ ] Migrated `emptiable_bound_pair`'s tests to jiff
  - [ ] Migrated `end_bound`'s tests to jiff
  - [ ] Migrated `finite_bound`'s tests to jiff
  - [ ] Migrated `half_bounded_interval`'s tests to jiff
  - [ ] Migrated `interval`'s tests to jiff
  - [ ] Migrated `start_bound`'s tests to jiff
- [ ] Migrated `intervals::relative`'s tests to jiff
  - [ ] Migrated `bound_pair`'s tests to jiff
  - [ ] Migrated `bound`'s tests to jiff
  - [ ] Migrated `bounded_interval`'s tests to jiff
  - [ ] Migrated `emptiable_bound_pair`'s tests to jiff
  - [ ] Migrated `end_bound`'s tests to jiff
  - [ ] Migrated `finite_bound`'s tests to jiff
  - [ ] Migrated `half_bounded_interval`'s tests to jiff
  - [ ] Migrated `interval`'s tests to jiff
  - [ ] Migrated `start_bound`'s tests to jiff
- [ ] Migrated `convenience::absolute`'s tests to jiff
- [ ] Migrated `convenience::relative`'s tests to jiff
- [ ] Migrated `intervals::special`'s tests to jiff
- [x] Migrated `time`'s tests to jiff
- [x] Migrated `ops`'s tests to jiff

- [ ] Migrated `intervals::absolute`'s examples to jiff
  - [ ] Migrated `bound_pair`'s examples to jiff
  - [ ] Migrated `bound`'s examples to jiff
  - [ ] Migrated `bounded_interval`'s examples to jiff
  - [ ] Migrated `emptiable_bound_pair`'s examples to jiff
  - [x] Migrated `end_bound`'s examples to jiff
  - [x] Migrated `finite_bound`'s examples to jiff
  - [ ] Migrated `half_bounded_interval`'s examples to jiff
  - [ ] Migrated `interval`'s examples to jiff
  - [x] Migrated `start_bound`'s examples to jiff
- [ ] Migrated `intervals::relative`'s examples to jiff
  - [ ] Migrated `bound_pair`'s examples to jiff
  - [ ] Migrated `bound`'s examples to jiff
  - [ ] Migrated `bounded_interval`'s examples to jiff
  - [ ] Migrated `emptiable_bound_pair`'s examples to jiff
  - [ ] Migrated `end_bound`'s examples to jiff
  - [ ] Migrated `finite_bound`'s examples to jiff
  - [ ] Migrated `half_bounded_interval`'s examples to jiff
  - [ ] Migrated `interval`'s examples to jiff
  - [ ] Migrated `start_bound`'s examples to jiff
- [ ] Migrated `convenience::absolute`'s examples to jiff
- [ ] Migrated `convenience::relative`'s examples to jiff
- [x] Migrated `intervals::special`'s examples to jiff
- [x] Migrated `ops`'s examples to jiff
- [ ] Migrated `intervals`'s examples to jiff

- [x] Updated `time` tests to check new structures
- [x] Finished `time` docs

- [ ] Renamed all occurrences of "from" and "to" to "start" and "end" respectively to avoid confusion
  and to make it easier to refer to ("start time" is more explicit than "from time")

- [x] Renamed `NaiveDuration` to `CalendarAnchorOffset`
- [x] Refactored `Precision` to contain a `Duration` and a `PrecisionMode`
- [x] Refactored `Precision::precise_time`

- [x] Split `absolute` and `relative` modules internally for better code management
- [ ] Split convenience methods for absolute/relative intervals into the `convenience` module
- [ ] Moved+Split `absolute_tests` to their new counterpart
- [ ] Moved+Split `relative_tests` to their new counterpart

## Deprecated

## Removed

## Fixed

## Security

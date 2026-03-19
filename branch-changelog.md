<!-- DELETE THIS FILE BEFORE CREATING PR -->

# Personal notes

- Check logic of absolute.rs and relative.rs to avoid confusion, especially since
  relative.rs has bounds that can be defined as two offsets OR one offset and a length
- Rename from/to times to start/end
- Rename "bounds" (plural) to bound pair
- Create migration guide/notes from 0.2 to 0.3

## Scope creep tasks to do in the future

- [ ] More conversions from specific intervals and bound pairs to other types
  - [ ] By implementing `From`/`TryFrom` on types
  - [ ] By implementing `to_x()` methods on types
- [ ] Replaced conversion errors from single-variant enums to tag structs
- [ ] (Internal) Replace `ExampleError` pattern by `Box<dyn Error>` to reduce hidden example size
- [ ] Add tests on new/untested methods to increase code coverage
- [ ] Add convenience method `.try_from_range()` on `BoundedAbsoluteInterval`
- [ ] Add convenience method `.try_from_range()` on `HalfBoundedAbsoluteInterval`
- [ ] Add convenience method `.try_from_range()` on `AbsoluteInterval`
- [ ] Add convenience method `.try_from_range()` on `EmptiableAbsoluteInterval`
- [ ] Add convenience method `.try_from_range()` on `BoundedRelativeInterval`
- [ ] Add convenience method `.try_from_range()` on `HalfBoundedRelativeInterval`
- [ ] Add convenience method `.try_from_range()` on `RelativeInterval`
- [ ] Add convenience method `.try_from_range()` on `EmptiableRelativeInterval`
- [ ] Add convenience methods on relative intervals similar to absolute intervals
- [ ] Re-express tests to more compact syntaxes using newly available convenience methods,
      such as `.to_start_bound()`, `.to_interval()`, etc.
- [ ] Review tests to ensure usefulness
- [ ] Add methods to get the `OffsetIsoWeek` of a given `Date`
  - [ ] Then re-implement convenience methods like `this_week`, `until_this_week` on intervals

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
- [x] Added convenience method `.to_start_bound()` to get a `RelativeStartBound` from a `RelativeFiniteBound`
- [x] Added convenience method `.to_end_bound()` to get a `RelativeEndBound` from a `RelativeFiniteBound`
- [x] Added convenience method `.to_interval()` on `BoundedAbsoluteInterval`
- [x] Added convenience method `.to_interval()` on `HalfBoundedAbsoluteInterval`
- [x] Added convenience method `.to_interval()` on `BoundedRelativeInterval`
- [x] Added convenience method `.to_interval()` on `HalfBoundedRelativeInterval`
- [x] Added a new `AbsoluteInterval` that doesn't allow for empty intervals
- [x] Added a new `RelativeInterval` that doesn't allow for empty intervals
- [x] Added method on `BoundedRelativeInterval` to create it from a start offset and length

## Changed

- [x] Migrated `intervals::absolute` to jiff
  - [x] Migrated `bound_pair` to jiff
  - [x] Migrated `bound` to jiff
  - [x] Migrated `bounded_interval` to jiff
  - [x] Migrated `emptiable_bound_pair` to jiff
  - [x] Migrated `end_bound` to jiff
  - [x] Migrated `finite_bound` to jiff
  - [x] Migrated `half_bounded_interval` to jiff
  - [x] Migrated `interval` to jiff
  - [x] Migrated `start_bound` to jiff
- [x] Migrated `intervals::relative` to jiff
  - [x] Migrated `bound_pair` to jiff
  - [x] Migrated `bound` to jiff
  - [x] Migrated `bounded_interval` to jiff
  - [x] Migrated `emptiable_bound_pair` to jiff
  - [x] Migrated `end_bound` to jiff
  - [x] Migrated `finite_bound` to jiff
  - [x] Migrated `half_bounded_interval` to jiff
  - [x] Migrated `interval` to jiff
  - [x] Migrated `start_bound` to jiff
- [x] Migrated `intervals::special` to jiff
- [x] Migrated `intervals::meta` to jiff
- [x] Migrated `intervals::bound_position` to jiff
- [x] Migrated `convenience::absolute` to jiff
  - [x] Migrated `convenience::absolute::bounded_interval` to jiff
  - [x] Migrated `convenience::absolute::half_bounded_interval` to jiff
- [x] Migrated `time` to jiff
- [x] Migrated `ops` to jiff
- [ ] Migrated `intervals::ops` to jiff
  - [ ] Migrated `abridge` to jiff
  - [ ] Migrated `bound_containment` to jiff
  - [ ] Migrated `complement` to jiff
  - [ ] Migrated `continuation` to jiff
  - [ ] Migrated `cut` to jiff
  - [ ] Migrated `extend` to jiff
  - [ ] Migrated `fill_gap` to jiff
  - [ ] Migrated `grow` to jiff
  - [ ] Migrated `overlap` to jiff
  - [ ] Migrated `point_containment` to jiff
  - [ ] Migrated `precision` to jiff
  - [ ] Migrated `relativity_conversion` to jiff
  - [ ] Migrated `remove_overlap_or_gap` to jiff
  - [ ] Migrated `remove_overlap` to jiff
  - [ ] Migrated `set_ops` to jiff
  - [ ] Migrated `shrink` to jiff
  - [ ] Migrated `split` to jiff

- [x] Migrated `intervals::absolute`'s tests to jiff
  - [x] Migrated `bound_pair`'s tests to jiff
  - [x] Migrated `bound`'s tests to jiff
  - [x] Migrated `bounded_interval`'s tests to jiff
  - [x] Migrated `emptiable_bound_pair`'s tests to jiff
  - [x] Migrated `end_bound`'s tests to jiff
  - [x] Migrated `finite_bound`'s tests to jiff
  - [x] Migrated `half_bounded_interval`'s tests to jiff
  - [x] Migrated `interval`'s tests to jiff
  - [x] Migrated `start_bound`'s tests to jiff
- [x] Migrated `intervals::relative`'s tests to jiff
  - [x] Migrated `bound_pair`'s tests to jiff
  - [x] Migrated `bound`'s tests to jiff
  - [x] Migrated `bounded_interval`'s tests to jiff
  - [x] Migrated `emptiable_bound_pair`'s tests to jiff
  - [x] Migrated `end_bound`'s tests to jiff
  - [x] Migrated `finite_bound`'s tests to jiff
  - [x] Migrated `half_bounded_interval`'s tests to jiff
  - [x] Migrated `interval`'s tests to jiff
  - [x] Migrated `start_bound`'s tests to jiff
- [x] Migrated `intervals::special`'s tests to jiff
- [x] Migrated `intervals::meta`'s tests to jiff
- [x] Migrated `intervals::bound_position`'s tests to jiff
- [x] Migrated `convenience::absolute`'s tests to jiff
  - [x] Migrated `convenience::absolute::bounded_interval`'s tests to jiff
  - [x] Migrated `convenience::absolute::half_bounded_interval`'s tests to jiff
- [x] Migrated `time`'s tests to jiff
- [x] Migrated `ops`'s tests to jiff
- [ ] Migrated `intervals::ops`'s tests to jiff
  - [ ] Migrated `abridge`'s tests to jiff
  - [ ] Migrated `bound_containment`'s tests to jiff
  - [x] Migrated `bound_ord`'s tests to jiff
  - [ ] Migrated `complement`'s tests to jiff
  - [ ] Migrated `continuation`'s tests to jiff
  - [ ] Migrated `cut`'s tests to jiff
  - [ ] Migrated `extend`'s tests to jiff
  - [ ] Migrated `fill_gap`'s tests to jiff
  - [ ] Migrated `grow`'s tests to jiff
  - [ ] Migrated `overlap`'s tests to jiff
  - [ ] Migrated `point_containment`'s tests to jiff
  - [ ] Migrated `precision`'s tests to jiff
  - [ ] Migrated `relativity_conversion`'s tests to jiff
  - [ ] Migrated `remove_overlap_or_gap`'s tests to jiff
  - [ ] Migrated `remove_overlap`'s tests to jiff
  - [ ] Migrated `set_ops`'s tests to jiff
  - [ ] Migrated `shrink`'s tests to jiff
  - [ ] Migrated `split`'s tests to jiff

- [x] Migrated `intervals::absolute`'s examples to jiff
  - [x] Migrated `bound_pair`'s examples to jiff
  - [x] Migrated `bound`'s examples to jiff
  - [x] Migrated `bounded_interval`'s examples to jiff
  - [x] Migrated `emptiable_bound_pair`'s examples to jiff
  - [x] Migrated `end_bound`'s examples to jiff
  - [x] Migrated `finite_bound`'s examples to jiff
  - [x] Migrated `half_bounded_interval`'s examples to jiff
  - [x] Migrated `interval`'s examples to jiff
  - [x] Migrated `start_bound`'s examples to jiff
- [x] Migrated `intervals::relative`'s examples to jiff
  - [x] Migrated `bound_pair`'s examples to jiff
  - [x] Migrated `bound`'s examples to jiff
  - [x] Migrated `bounded_interval`'s examples to jiff
  - [x] Migrated `emptiable_bound_pair`'s examples to jiff
  - [x] Migrated `end_bound`'s examples to jiff
  - [x] Migrated `finite_bound`'s examples to jiff
  - [x] Migrated `half_bounded_interval`'s examples to jiff
  - [x] Migrated `interval`'s examples to jiff
  - [x] Migrated `start_bound`'s examples to jiff
- [x] Migrated `intervals::special`'s examples to jiff
- [x] Migrated `intervals::meta`'s examples to jiff
- [x] Migrated `intervals::bound_position`'s examples to jiff
- [x] Migrated `convenience::absolute`'s examples to jiff
  - [x] Migrated `convenience::absolute::bounded_interval`'s examples to jiff
  - [x] Migrated `convenience::absolute::half_bounded_interval`'s examples to jiff
- [x] Migrated `ops`'s examples to jiff
- [x] Migrated `intervals`'s examples to jiff
- [ ] Migrated `intervals::ops`'s examples to jiff
  - [ ] Migrated `abridge`'s examples to jiff
  - [ ] Migrated `bound_containment`'s examples to jiff
  - [ ] Migrated `bound_ord`'s examples to jiff
  - [ ] Migrated `bound_overlap_ambiguity`'s examples to jiff
  - [ ] Migrated `complement`'s examples to jiff
  - [ ] Migrated `continuation`'s examples to jiff
  - [ ] Migrated `cut`'s examples to jiff
  - [ ] Migrated `extend`'s examples to jiff
  - [ ] Migrated `fill_gap`'s examples to jiff
  - [ ] Migrated `grow`'s examples to jiff
  - [ ] Migrated `overlap`'s examples to jiff
  - [ ] Migrated `point_containment`'s examples to jiff
  - [ ] Migrated `precision`'s examples to jiff
  - [ ] Migrated `relativity_conversion`'s examples to jiff
  - [ ] Migrated `remove_overlap_or_gap`'s examples to jiff
  - [ ] Migrated `remove_overlap`'s examples to jiff
  - [ ] Migrated `set_ops`'s examples to jiff
  - [ ] Migrated `shrink`'s examples to jiff
  - [ ] Migrated `split`'s examples to jiff

- [x] Updated `time` tests to check new structures
- [x] Finished `time` docs

- [x] Changed `BoundedRelativeInterval` to have a start and end offset

- [ ] Renamed all occurrences of "from" and "to" to "start" and "end" respectively to avoid confusion
  and to make it easier to refer to ("start time" is more explicit than "from time")
- [x] Renamed "bounds" to "bound pair"

- [x] Renamed `NaiveDuration` to `CalendarAnchorOffset`
- [x] Refactored `Precision` to contain a `Duration` and a `PrecisionMode`
- [x] Refactored `Precision::precise_time`

- [x] Split `absolute` and `relative` modules internally for better code management
- [x] Split convenience methods for absolute intervals into the `convenience` module
- [x] Moved+Split `absolute_tests` to their new counterpart
- [x] Moved+Split `relative_tests` to their new counterpart

- [x] Renamed `AbsoluteInterval` to `EmptiableAbsoluteInterval`
- [x] Renamed `RelativeInterval` to `EmptiableRelativeInterval`

## Deprecated

## Removed

- Removed `Display` implementations on intervals and related types in favor of more specialized
  formatting methods (WIP)
- Removed convenience methods (+ related tests) that converted a `Date` to an `OffsetIsoWeek`

## Fixed

## Security

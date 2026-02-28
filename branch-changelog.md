<!-- DELETE THIS FILE BEFORE CREATING PR -->

# Personal notes

- Check logic of absolute.rs and relative.rs to avoid confusion, especially since
  relative.rs has bounds that can be defined as two offsets OR one offset and a length
- Renamed from/to times to start/end

# Changelog

## Added

- [ ] Added rough `NaiveWeek` structure as a drop-in replacement for `chrono`'s `NaiveWeek`
- [ ] Added `NaiveIsoWeek`

## Changed

- [ ] Migrating `absolute.rs` to jiff
- [ ] Migrating `relative.rs` to jiff
- [ ] Migrating `special.rs` to jiff
- [ ] Migrating `time.rs` to jiff
- [ ] Migrating `ops.rs` to jiff

- [ ] Migrating `absolute.rs`'s tests to jiff
- [ ] Migrating `relative.rs`'s tests to jiff
- [ ] Migrating `special.rs`'s tests to jiff
- [ ] Migrating `time.rs`'s tests to jiff
- [ ] Migrating `ops.rs`'s tests to jiff

- [ ] Migrating `absolute.rs`'s examples to jiff
- [ ] Migrating `relative.rs`'s examples to jiff
- [ ] Migrating `special.rs`'s examples to jiff
- [ ] Migrating `time.rs`'s examples to jiff
- [ ] Migrating `ops.rs`'s examples to jiff

- [ ] Renamed all occurrences of "from" and "to" to "start" and "end" respectively to avoid confusion
  and to make it easier to refer to ("start time" is more explicit than "from time")

## Deprecated

## Removed

## Fixed

## Security

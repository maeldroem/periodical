<div align="center">

<h1>:clock4: <code>periodical</code> :clock7:</h1>

[![crates.io](https://img.shields.io/crates/v/periodical)](https://crates.io/crates/periodical)
[![libs.rs](https://img.shields.io/badge/libs.rs-periodical-blue)](https://lib.rs/periodical)
[![Periodical documentation](https://docs.rs/periodical/badge.svg)](https://docs.rs/periodical)
[![build status](https://github.com/maeldroem/periodical/actions/workflows/rust.yml/badge.svg?branch=main)](https://github.com/maeldroem/periodical/actions)

:two_hearts: <a href="https://github.com/sponsors/maeldroem"><img src="https://img.shields.io/badge/Sponsor-%E2%9D%A4-%23db61a2.svg?&logo=github&logoColor=white&labelColor=181717&style=flat-square" alt="GitHub Sponsor" height="30" /></a> :two_hearts:

</div>

`periodical` is a crate to manage absolute and relative time intervals, use it to manage schedules, find overlaps,
and more!

Just add the following in your `Cargo.toml` to start using `periodical` in your project!

```toml
periodical = "0.1"
```

# About :book:

:watch: Time intervals are very important in many fields and applications, this is why this crate was made.

It manages time intervals precisely. It takes care of bound inclusivities and supports half-bounded and unbounded
intervals.

:dart: It also provides precise ways to not only check for overlap between two intervals, but also find what kind of overlap
exists!

Since bound inclusivities can introduce ambiguity for what we consider and overlap or containment, the crate provides
many ways to disambiguate those cases in the way way <ins>you</ins> want.

This allows for treating a day as it really is: From midnight, included, to the next midnight, excluded.
And still receive precise data about its duration and if it's adjacent to another day's interval.

:arrow_right: No more problems with flaky overlap checks and context-dependent durations!

`periodical` also allows you to re-precise an interval to your liking. For example, if you have to keep a timelog
where the bounds have to be rounded to the nearest 45 minutes, you can do it with `periodical`!
It also supports precising bounds individually and with durations that are not divisors of 24 hours :sunglasses:.

Most of the things you can think of doing with time intervals, you can do it with `periodical` :sparkles:

And if it doesn't, feel absolutely free to [contribute](CONTRIBUTING.md) or [suggest a change](CONTRIBUTING.md) :smile:

# Roadmap :soon:

## 0.1.0

- [x] Tests
- [x] Test coverage
- [x] [`arbitrary`](https://lib.rs/arbitrary) support
- [x] Fuzzing
- [ ] Full-fledged documentation
- [x] Conversion methods to create `periodical`-specific types from standard types

## Future

- [ ] [`serde`](https://lib.rs/serde) support :1234:
- [ ] Convenience methods for creating common intervals with ease :chart_with_upwards_trend:
- [ ] Interval periodicity :repeat:
- [ ] Implementation of [`rayon`](https://lib.rs/rayon) for lightning-fast iterators :zap:
- [ ] Epsilon support for interval durations
- [ ] [Cargo mutants](https://lib.rs/crates/cargo-mutants)

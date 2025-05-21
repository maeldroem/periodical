use chrono::Duration;

/// Time precision used for comparisons
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Precision {
    /// Rounds the compared times to the given duration (e.g. if the duration is 1 second, the times will be rounded to the nearest second)
    ToNearest(Duration),
    /// Floors the compared times to the given duration (e.g. if the duration is 5 minutes, the times will be floored to the 5-minutes part they are in)
    ToPast(Duration),
    /// Ceils the compared times to the given duration
    ToFuture(Duration),
}

/// Where the given time was found relative to a time interval
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ContainmentPosition {
    /// The given time was found before the time interval's beginning
    OutsideBefore,
    /// The given time was found after the time interval's end
    OutsideAfter,
    /// The given time was found outside the time interval (result only possible when dealing with empty intervals)
    Outside,
    /// The given time was found exactly on the start of the time interval
    OnStart,
    /// The given time was found exactly on the end of the time interval
    OnEnd,
    /// The given time was found within the time interval
    Inside,
}

/// Where the other time interval was found relative to the current time interval
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum OverlapPosition {
    /// The given other time interval was found before the time interval
    OutsideBefore,
    /// The given other time interval was found after the time interval
    OutsideAfter,
    /// The given other time interval was found outside the time interval (result only possible when dealing with empty intervals)
    Outside,
    /// The given other time interval was found ending on the beginning of the time interval
    OnStart,
    /// The given other time interval was found starting on the end of the time interval
    OnEnd,
    /// The given other time interval was found beginning outside the time interval but ending inside
    CrossesStart,
    /// The given other time interval was found beginning inside the time interval but ending outside
    CrossesEnd,
    /// The given other time interval was found completely inside the time interval
    Inside,
    /// The given other time interval was found beginning on the start of of the time interval and ending inside the time interval
    InsideAndSameStart,
    /// The given other time interval was found beginning inside the time interval and ending at the end of the time interval
    InsideAndSameEnd,
    /// The given other time interval was found beginning and ending at the same times as the time interval
    Equal,
    /// The given other time interval was found beginning on the same point as the time interval and ending after the time interval
    ContainsAndSameStart,
    /// The given other time interval was found beginning before the time interval and ending at the same time as the time interval
    ContainsAndSameEnd,
    /// The given other time interval was found beginning before the time interval's start and ending after the time interval's end
    Contains,
}

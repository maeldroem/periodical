//! Interval splittability
//!
//! # Splitting by [`NaiveDuration`]
//!
//! Practical approach for splitting an interval into common human naive durations, such as days and weeks.
//! As explained in [`NaiveDuration`], days, weeks, etc. don't have a constant length.
//!
//! You can produce a [`CalendarAnchorOffsetSplit`] iterator by calling
//! [`split_by_naive_duration`](CalendarAnchorOffsetSplittable::split_by_naive_duration) which will split the interval
//! in chronological order.
//!
//! You can also produce a [`CalendarAnchorOffsetRSplit`] iterator by calling
//! [`rsplit_by_naive_duration`](CalendarAnchorOffsetSplittable::rsplit_by_naive_duration) which will split the interval
//! in reverse chronological order.
//!
//! # Splitting by [`BoundedRelativeInterval`]
//!
//! Approach for splitting an interval into splits of precise duration using a [`BoundedRelativeInterval`]
//! as a reference.
//!
//! The provided [`IntervalSplit`] iterator, which is produced by
//! [`split_by_interval`](IntervalSplittable::split_by_interval),
//! will process this splitting approach.
//!
//! Since this iterator takes a [`BoundedRelativeInterval`] which has [bound inclusivities](BoundInclusivity),
//! the resulting splits will reflect the same bound inclusivities as the reference, out of convenience.

// TODO UPDATE MODULE OUTER DOC

use std::cmp::Ordering;

use jiff::Timestamp;
use jiff::tz::TimeZone;

use crate::intervals::absolute::{BoundedAbsoluteInterval, HalfBoundedAbsoluteInterval, HasAbsoluteBoundPair};
use crate::iter::intervals::split::CalendarAnchorOffsetSplit;
use crate::time::CalendarAnchorOffset;

/// A [`CalendarAnchorOffsetSplit`]'s result
///
/// Depending on the interval being split, it can result in different kinds of splits.
///
/// This enum groups them in one common structure so that it gives the caller the freedom to choose
/// which to keep and which to filter out without having to consult the contained interval's data.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CalendarAnchorOffsetSplitResult {
    /// Infinite split
    ///
    /// This is the result of splitting a
    /// [`HalfBoundedAbsoluteInterval`](crate::intervals::absolute::HalfBoundedAbsoluteInterval).
    ///
    /// If we have a half-bounded interval, with its opening direction being
    /// [`ToPast`](crate::intervals::meta::OpeningDirection::ToPast), then the [`CalendarAnchorOffsetSplit`] iterator
    /// will produce such a result spanning from the relevant time extremity, here minus infinity, to the closest
    /// relevant representable point in time, in this case, [`Timestamp::MIN`].
    Infinite(HalfBoundedAbsoluteInterval),
    /// Full split
    ///
    /// A split of the expected duration.
    Full(BoundedAbsoluteInterval),
    /// Partial split
    ///
    /// The remainder of the interval splitting process.
    Partial(BoundedAbsoluteInterval),
}

impl CalendarAnchorOffsetSplitResult {
    /// Returns the content of the [`Infinite`](CalendarAnchorOffsetSplitResult::Infinite) variant
    ///
    /// Consumes `self` and puts the content of the [`Infinite`](CalendarAnchorOffsetSplitResult::Infinite) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, HalfBoundedAbsoluteInterval};
    /// # use periodical::intervals::meta::OpeningDirection;
    /// # use periodical::intervals::ops::split::CalendarAnchorOffsetSplitResult;
    /// let infinite_split = HalfBoundedAbsoluteInterval::new(
    ///     "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     OpeningDirection::ToPast,
    /// );
    /// let infinite_result = CalendarAnchorOffsetSplitResult::Infinite(infinite_split.clone());
    ///
    /// let full_split = BoundedAbsoluteInterval::new(
    ///     "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     "2026-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// );
    /// let full_result = CalendarAnchorOffsetSplitResult::Full(full_split);
    ///
    /// assert_eq!(infinite_result.infinite(), Some(infinite_split));
    /// assert_eq!(full_result.infinite(), None);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn infinite(self) -> Option<HalfBoundedAbsoluteInterval> {
        match self {
            Self::Infinite(x) => Some(x),
            _ => None,
        }
    }

    /// Returns the content of the [`Full`](CalendarAnchorOffsetSplitResult::Full) variant
    ///
    /// Consumes `self` and puts the content of the [`Full`](CalendarAnchorOffsetSplitResult::Full) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, HalfBoundedAbsoluteInterval};
    /// # use periodical::intervals::meta::OpeningDirection;
    /// # use periodical::intervals::ops::split::CalendarAnchorOffsetSplitResult;
    /// let full_split = BoundedAbsoluteInterval::new(
    ///     "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     "2026-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// );
    /// let full_result = CalendarAnchorOffsetSplitResult::Full(full_split.clone());
    ///
    /// let infinite_split = HalfBoundedAbsoluteInterval::new(
    ///     "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     OpeningDirection::ToPast,
    /// );
    /// let infinite_result = CalendarAnchorOffsetSplitResult::Infinite(infinite_split);
    ///
    /// assert_eq!(full_result.full(), Some(full_split));
    /// assert_eq!(infinite_result.full(), None);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn full(self) -> Option<BoundedAbsoluteInterval> {
        match self {
            Self::Full(x) => Some(x),
            _ => None,
        }
    }

    /// Returns the content of the [`Partial`](CalendarAnchorOffsetSplitResult::Partial) variant
    ///
    /// Consumes `self` and puts the content of the [`Partial`](CalendarAnchorOffsetSplitResult::Partial) variant
    /// in an [`Option`]. If instead `self` is another variant, the method returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, HalfBoundedAbsoluteInterval};
    /// # use periodical::intervals::meta::OpeningDirection;
    /// # use periodical::intervals::ops::split::CalendarAnchorOffsetSplitResult;
    /// let partial_split = BoundedAbsoluteInterval::new(
    ///     "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     "2026-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// );
    /// let partial_result = CalendarAnchorOffsetSplitResult::Partial(partial_split.clone());
    ///
    /// let infinite_split = HalfBoundedAbsoluteInterval::new(
    ///     "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     OpeningDirection::ToPast,
    /// );
    /// let infinite_result = CalendarAnchorOffsetSplitResult::Infinite(infinite_split);
    ///
    /// assert_eq!(partial_result.partial(), Some(partial_split));
    /// assert_eq!(infinite_result.partial(), None);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn partial(self) -> Option<BoundedAbsoluteInterval> {
        match self {
            Self::Partial(x) => Some(x),
            _ => None,
        }
    }

    /// Returns whether it is of the [`Infinite`](CalendarAnchorOffsetSplitResult::Infinite) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, HalfBoundedAbsoluteInterval};
    /// # use periodical::intervals::meta::OpeningDirection;
    /// # use periodical::intervals::ops::split::CalendarAnchorOffsetSplitResult;
    /// let infinite_split = HalfBoundedAbsoluteInterval::new(
    ///     "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     OpeningDirection::ToPast,
    /// );
    /// let infinite_result = CalendarAnchorOffsetSplitResult::Infinite(infinite_split);
    ///
    /// let full_split = BoundedAbsoluteInterval::new(
    ///     "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     "2026-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// );
    /// let full_result = CalendarAnchorOffsetSplitResult::Full(full_split);
    ///
    /// assert!(infinite_result.is_infinite());
    /// assert!(!full_result.is_infinite());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_infinite(&self) -> bool {
        matches!(self, Self::Infinite(_))
    }

    /// Returns whether it is of the [`Full`](CalendarAnchorOffsetSplitResult::Full) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, HalfBoundedAbsoluteInterval};
    /// # use periodical::intervals::meta::OpeningDirection;
    /// # use periodical::intervals::ops::split::CalendarAnchorOffsetSplitResult;
    /// let full_split = BoundedAbsoluteInterval::new(
    ///     "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     "2026-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// );
    /// let full_result = CalendarAnchorOffsetSplitResult::Full(full_split);
    ///
    /// let infinite_split = HalfBoundedAbsoluteInterval::new(
    ///     "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     OpeningDirection::ToPast,
    /// );
    /// let infinite_result = CalendarAnchorOffsetSplitResult::Infinite(infinite_split);
    ///
    /// assert!(full_result.is_full());
    /// assert!(!infinite_result.is_full());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_full(&self) -> bool {
        matches!(self, Self::Full(_))
    }

    /// Returns whether it is of the [`Full`](CalendarAnchorOffsetSplitResult::Full) variant
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Zoned;
    /// # use periodical::intervals::absolute::{BoundedAbsoluteInterval, HalfBoundedAbsoluteInterval};
    /// # use periodical::intervals::meta::OpeningDirection;
    /// # use periodical::intervals::ops::split::CalendarAnchorOffsetSplitResult;
    /// let partial_split = BoundedAbsoluteInterval::new(
    ///     "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     "2026-01-02 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    /// );
    /// let partial_result = CalendarAnchorOffsetSplitResult::Partial(partial_split);
    ///
    /// let infinite_split = HalfBoundedAbsoluteInterval::new(
    ///     "2026-01-01 00:00:00[Europe/Oslo]".parse::<Zoned>()?.timestamp(),
    ///     OpeningDirection::ToPast,
    /// );
    /// let infinite_result = CalendarAnchorOffsetSplitResult::Infinite(infinite_split);
    ///
    /// assert!(partial_result.is_partial());
    /// assert!(!infinite_result.is_partial());
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn is_partial(&self) -> bool {
        matches!(self, Self::Partial(_))
    }
}

impl PartialOrd for CalendarAnchorOffsetSplitResult {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CalendarAnchorOffsetSplitResult {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::Infinite(_), Self::Infinite(_))
            | (Self::Full(_), Self::Full(_))
            | (Self::Partial(_), Self::Partial(_)) => Ordering::Equal,
            (Self::Infinite(_), _) | (Self::Full(_), Self::Partial(_)) => Ordering::Greater,
            (Self::Full(_), Self::Infinite(_)) | (Self::Partial(_), _) => Ordering::Less,
        }
    }
}

/// Dispatcher trait for the [`CalendarAnchorOffsetSplit`] and [`CalendarAnchorOffsetRSplit`] iterators
pub trait CalendarAnchorOffsetSplittable
where
    Self: Sized,
{
    fn split_by_calendar_anchor_offset(self, calendar_anchor_offset: CalendarAnchorOffset, tz: TimeZone) -> CalendarAnchorOffsetSplit;

    // fn rsplit_by_calendar_anchor_offset(self, calendar_anchor_offset: CalendarAnchorOffset, tz: TimeZone) -> CalendarAnchorOffsetRSplit;
}

impl<T> CalendarAnchorOffsetSplittable for T
where
    T: HasAbsoluteBoundPair,
{
    fn split_by_calendar_anchor_offset(self, calendar_anchor_offset: CalendarAnchorOffset, tz: TimeZone) -> CalendarAnchorOffsetSplit {
        CalendarAnchorOffsetSplit::new(&self, calendar_anchor_offset, tz)
    }
}

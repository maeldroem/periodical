//! Bound positioning within a collection of intervals
//!
//! This module contains [`BoundPosition`], which allows for tracking bounds
//! across a collection of intervals. This is used by iterators in this crate,
//! but can also be used in other places to share a bound position.

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::intervals::absolute::{AbsoluteBound, HasAbsoluteBoundPair};
use crate::intervals::relative::{HasRelativeBoundPair, RelativeBound};

/// Type and index of the positioned bound
///
/// This enumerator contains variants for describing the type of the positioned
/// bound, and inside those variants we find a [`usize`] describing the index of
/// the interval containing the positioned bound.
///
/// <div class="warning">
/// **Warning**
///
/// This object could be subject to change in future versions,
/// for example by switching to a structure containing a field for the bound
/// type (Start/End), and a field for the interval index.
/// </div>
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum BoundPosition {
    Start(usize),
    End(usize),
}

impl BoundPosition {
    /// Maximum bound position
    pub const MAX: Self = BoundPosition::End(usize::MAX);
    /// Minimum bound position
    pub const MIN: Self = BoundPosition::Start(usize::MIN);

    /// Returns the interval index
    #[must_use]
    pub fn index(&self) -> usize {
        match self {
            Self::Start(i) | Self::End(i) => *i,
        }
    }

    /// Returns the [`AbsoluteBound`] corresponding to the bound position
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jiff::Timestamp;
    /// # use periodical::intervals::absolute::{
    /// #     AbsoluteBound, AbsoluteBoundPair, AbsoluteEndBound, AbsoluteFiniteBoundPosition, AbsoluteStartBound,
    /// # };
    /// # use periodical::intervals::bound_position::BoundPosition;
    /// let abs_bounds = [
    ///     AbsoluteBoundPair::new(AbsoluteStartBound::InfinitePast, AbsoluteEndBound::InfiniteFuture),
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 08:00:00Z".parse::<Timestamp>()?,
    ///         ).to_start_bound(),
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 11:00:00Z".parse::<Timestamp>()?,
    ///         ).to_end_bound(),
    ///     ),
    ///     AbsoluteBoundPair::new(
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 13:00:00Z".parse::<Timestamp>()?,
    ///         ).to_start_bound(),
    ///         AbsoluteFiniteBoundPosition::new(
    ///             "2025-01-01 16:00:00Z".parse::<Timestamp>()?,
    ///         ).to_end_bound(),
    ///     ),
    /// ];
    ///
    /// let positioned_bound = BoundPosition::End(1).get_abs_bound(&abs_bounds);
    /// let expected_bound = AbsoluteFiniteBoundPosition::new(
    ///     "2025-01-01 11:00:00Z".parse::<Timestamp>()?,
    /// ).to_end_bound().to_bound();
    ///
    /// assert_eq!(positioned_bound, Some(expected_bound));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[must_use]
    pub fn get_abs_bound<'j, I, J>(&self, abs_bounds: I) -> Option<AbsoluteBound>
    where
        I: IntoIterator<Item = &'j J>,
        J: 'j + HasAbsoluteBoundPair,
    {
        match self {
            Self::Start(i) => abs_bounds
                .into_iter()
                .nth(*i)
                .map(|bounds| bounds.abs_start().to_bound()),
            Self::End(i) => abs_bounds.into_iter().nth(*i).map(|bounds| bounds.abs_end().to_bound()),
        }
    }

    /// Returns the [`RelativeBound`] corresponding to the bound position
    ///
    /// # Examples
    ///
    /// ```
    /// # use jiff::SignedDuration;
    /// # use periodical::intervals::relative::{
    /// #     RelativeBound, RelativeBoundPair, RelativeEndBound, RelativeFiniteBoundPosition, RelativeStartBound,
    /// # };
    /// # use periodical::intervals::bound_position::BoundPosition;
    /// let rel_bounds = [
    ///     RelativeBoundPair::new(RelativeStartBound::InfinitePast, RelativeEndBound::InfiniteFuture),
    ///     RelativeBoundPair::new(
    ///         RelativeFiniteBoundPosition::new(
    ///             SignedDuration::from_hours(8),
    ///         ).to_start_bound(),
    ///         RelativeFiniteBoundPosition::new(
    ///             SignedDuration::from_hours(11),
    ///         ).to_end_bound(),
    ///     ),
    ///     RelativeBoundPair::new(
    ///         RelativeFiniteBoundPosition::new(
    ///             SignedDuration::from_hours(13),
    ///         ).to_start_bound(),
    ///         RelativeFiniteBoundPosition::new(
    ///             SignedDuration::from_hours(16),
    ///         ).to_end_bound(),
    ///     ),
    /// ];
    ///
    /// let positioned_bound = BoundPosition::End(1).get_rel_bound(&rel_bounds);
    /// let expected_bound = RelativeFiniteBoundPosition::new(
    ///     SignedDuration::from_hours(11),
    /// ).to_end_bound().to_bound();
    ///
    /// assert_eq!(positioned_bound, Some(expected_bound));
    /// ```
    #[must_use]
    pub fn get_rel_bound<'j, I, J>(&self, rel_bounds: I) -> Option<RelativeBound>
    where
        I: IntoIterator<Item = &'j J>,
        J: 'j + HasRelativeBoundPair,
    {
        match self {
            Self::Start(i) => rel_bounds
                .into_iter()
                .nth(*i)
                .map(|bounds| bounds.rel_start().to_bound()),
            Self::End(i) => rel_bounds.into_iter().nth(*i).map(|bounds| bounds.rel_end().to_bound()),
        }
    }

    /// Adds the given amount to the interval index
    ///
    /// Returns whether the position has hit its maximum
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::bound_position::BoundPosition;
    /// let mut bound_position = BoundPosition::Start(4);
    /// bound_position.add_interval_index(3);
    ///
    /// assert_eq!(bound_position, BoundPosition::Start(7));
    /// ```
    pub fn add_interval_index(&mut self, count: usize) -> bool {
        match self {
            Self::Start(i) | Self::End(i) => {
                if let Some(new_i) = i.checked_add(count) {
                    *i = new_i;
                    false
                } else {
                    *self = Self::MAX;
                    true
                }
            },
        }
    }

    /// Subtracts the given amount to the interval index
    ///
    /// Returns whether the position has hit its minimum
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::bound_position::BoundPosition;
    /// let mut bound_position = BoundPosition::Start(4);
    /// bound_position.sub_interval_index(3);
    ///
    /// assert_eq!(bound_position, BoundPosition::Start(1));
    /// ```
    pub fn sub_interval_index(&mut self, count: usize) -> bool {
        match self {
            Self::Start(i) | Self::End(i) => {
                if let Some(new_i) = i.checked_sub(count) {
                    *i = new_i;
                    false
                } else {
                    *self = Self::MIN;
                    true
                }
            },
        }
    }

    /// Increments the interval index
    ///
    /// Returns whether the position has hit its maximum
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::bound_position::BoundPosition;
    /// let mut bound_position = BoundPosition::Start(4);
    /// bound_position.increment_interval_index();
    ///
    /// assert_eq!(bound_position, BoundPosition::Start(5));
    /// ```
    pub fn increment_interval_index(&mut self) -> bool {
        self.add_interval_index(1)
    }

    /// Decrements the interval index
    ///
    /// Returns whether the position has hits its minimum
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::bound_position::BoundPosition;
    /// let mut bound_position = BoundPosition::Start(4);
    /// bound_position.decrement_interval_index();
    ///
    /// assert_eq!(bound_position, BoundPosition::Start(3));
    /// ```
    pub fn decrement_interval_index(&mut self) -> bool {
        self.sub_interval_index(1)
    }

    /// Advances the bound position by the given count
    ///
    /// Returns whether the position has hit its maximum
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::bound_position::BoundPosition;
    /// let mut bound_position = BoundPosition::Start(4);
    /// bound_position.advance_by(3);
    ///
    /// assert_eq!(bound_position, BoundPosition::End(5));
    /// ```
    pub fn advance_by(&mut self, count: usize) -> bool {
        if count.is_multiple_of(2) {
            match self {
                Self::Start(i) => {
                    if let Some(new_i) = i.checked_add(count.saturating_div(2)) {
                        *self = Self::Start(new_i);
                        false
                    } else {
                        *self = Self::MAX;
                        true
                    }
                },
                Self::End(i) => {
                    if let Some(new_i) = i.checked_add(count.saturating_div(2)) {
                        *self = Self::End(new_i);
                        false
                    } else {
                        *self = Self::MAX;
                        true
                    }
                },
            }
        } else {
            match self {
                Self::Start(i) => {
                    if let Some(new_i) = i.checked_add(count.saturating_div(2)) {
                        *self = Self::End(new_i);
                        false
                    } else {
                        *self = Self::MAX;
                        true
                    }
                },
                Self::End(i) => {
                    if let Some(new_i) = i.checked_add(count.saturating_div(2).saturating_add(1)) {
                        *self = Self::Start(new_i);
                        false
                    } else {
                        *self = Self::MAX;
                        true
                    }
                },
            }
        }
    }

    /// Advances back the bound position by the given count
    ///
    /// Returns whether the position has hit its minimum
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::bound_position::BoundPosition;
    /// let mut bound_position = BoundPosition::Start(4);
    /// bound_position.advance_back_by(3);
    ///
    /// assert_eq!(bound_position, BoundPosition::End(2));
    /// ```
    pub fn advance_back_by(&mut self, count: usize) -> bool {
        if count.is_multiple_of(2) {
            match self {
                Self::Start(i) => {
                    if let Some(new_i) = i.checked_sub(count.saturating_div(2)) {
                        *self = Self::Start(new_i);
                        false
                    } else {
                        *self = Self::MIN;
                        true
                    }
                },
                Self::End(i) => {
                    if let Some(new_i) = i.checked_sub(count.saturating_div(2)) {
                        *self = Self::End(new_i);
                        false
                    } else {
                        *self = Self::MIN;
                        true
                    }
                },
            }
        } else {
            match self {
                Self::Start(i) => {
                    if let Some(new_i) = i.checked_sub(count.saturating_div(2).saturating_add(1)) {
                        *self = Self::End(new_i);
                        false
                    } else {
                        *self = Self::MIN;
                        true
                    }
                },
                Self::End(i) => {
                    if let Some(new_i) = i.checked_sub(count.saturating_div(2)) {
                        *self = Self::Start(new_i);
                        false
                    } else {
                        *self = Self::MIN;
                        true
                    }
                },
            }
        }
    }

    /// Increments the bound position
    ///
    /// Returns whether the position has hit its maximum
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::bound_position::BoundPosition;
    /// let mut bound_position = BoundPosition::Start(4);
    /// bound_position.next_bound();
    ///
    /// assert_eq!(bound_position, BoundPosition::End(4));
    /// ```
    pub fn next_bound(&mut self) -> bool {
        self.advance_by(1)
    }

    /// Decrements the bound position
    ///
    /// Returns whether the position has hit its minimum
    ///
    /// # Examples
    ///
    /// ```
    /// # use periodical::intervals::bound_position::BoundPosition;
    /// let mut bound_position = BoundPosition::Start(4);
    /// bound_position.prev_bound();
    ///
    /// assert_eq!(bound_position, BoundPosition::End(3));
    /// ```
    pub fn prev_bound(&mut self) -> bool {
        self.advance_back_by(1)
    }
}

impl Default for BoundPosition {
    fn default() -> Self {
        BoundPosition::MIN
    }
}

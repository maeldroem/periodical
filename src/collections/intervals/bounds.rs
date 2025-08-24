//! Iterator over bounds of a unite interval set

use crate::intervals::absolute::AbsoluteBound;
use crate::intervals::relative::RelativeBound;
use crate::prelude::{AbsoluteBounds, RelativeBounds, HasAbsoluteBounds, HasRelativeBounds};

/// Type and index of the positioned bound
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoundPosition {
    Start(usize),
    End(usize),
}

impl BoundPosition {
    /// Returns the index of the bound position
    #[must_use]
    pub fn index(&self) -> usize {
        match self {
            Self::Start(i) | Self::End(i) => *i,
        }
    }

    /// Returns the [`AbsoluteBound`] corresponding to the bound position
    #[must_use]
    pub fn get_abs_bound(&self, abs_bounds: &[&AbsoluteBounds]) -> Option<AbsoluteBound> {
        match self {
            Self::Start(i) => abs_bounds.get(*i).map(|bounds| AbsoluteBound::Start(bounds.abs_start())),
            Self::End(i) => abs_bounds.get(*i).map(|bounds| AbsoluteBound::End(bounds.abs_end())),
        }
    }

    /// Returns the [`RelativeBound`] corresponding to the bound position
    #[must_use]
    pub fn get_rel_bound(&self, rel_bounds: &[&RelativeBounds]) -> Option<RelativeBound> {
        match self {
            Self::Start(i) => rel_bounds.get(*i).map(|bounds| RelativeBound::Start(bounds.rel_start())),
            Self::End(i) => rel_bounds.get(*i).map(|bounds| RelativeBound::End(bounds.rel_end())),
        }
    }

    /// Advances the bound position by increasing the bound index by the given count
    /// 
    /// Returns whether the position has hit its maximum
    pub fn advance_bounds_index_by(&mut self, count: usize) -> bool {
        // ACK: Yes, we are using saturating operations so that it doesn't panic if usize overflows
        match self {
            Self::Start(i) | Self::End(i) => {
                if let Some(new_i) = i.checked_add(count) {
                    *i = new_i;
                    false
                } else {
                    *i = usize::MAX;
                    true
                }
            },
        }
    }

    /// Advances back the bound position by decreasing the bound index by the given count
    /// 
    /// Returns whether the position has hit its minimum
    pub fn advance_back_bounds_index_by(&mut self, count: usize) -> bool {
        // ACK: Yes, we are using strict operations so that it doesn't panic if usize underflows
        match self {
            Self::Start(i) | Self::End(i) => {
                if let Some(new_i) = i.checked_sub(count) {
                    *i = new_i;
                    false
                } else {
                    *i = usize::MIN;
                    true
                }
            },
        }
    }

    /// Increments the bound index
    /// 
    /// Returns whether the position has hit its maximum
    pub fn next_by_bounds_index(&mut self) -> bool {
        self.advance_bounds_index_by(1)
    }

    /// Decrements the bound index
    /// 
    /// Returns whether the position has hits its minimum
    pub fn next_back_by_bounds_index(&mut self) -> bool {
        self.advance_back_bounds_index_by(1)
    }

    /// Advances the bound position by the given count of bounds to advance by
    /// 
    /// Returns whether the position has hit its maximum
    pub fn advance_by(&mut self, count: usize) -> bool {
        if count.is_multiple_of(2) {
            match self {
                Self::Start(i) => {
                    if let Some(new_i) = i.checked_add(count.saturating_div(2)) {
                        *self = Self::Start(new_i);
                        false
                    } else {
                        *self = Self::Start(usize::MAX);
                        true
                    }
                },
                Self::End(i) => {
                    if let Some(new_i) = i.checked_add(count.saturating_div(2)) {
                        *self = Self::End(new_i);
                        false
                    } else {
                        *self = Self::End(usize::MAX);
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
                        *self = Self::End(usize::MAX);
                        true
                    }
                },
                Self::End(i) => {
                    if let Some(new_i) = i.checked_add(count.saturating_div(2)) {
                        *self = Self::Start(new_i);
                        false
                    } else {
                        *self = Self::Start(usize::MAX);
                        true
                    }
                },
            }
        }
    }

    /// Advances back the bound position by the given count of bounds to advance back by
    /// 
    /// Returns whether the position has hit its minimum
    pub fn advance_back_by(&mut self, count: usize) -> bool {
        if count.is_multiple_of(2) {
            match self {
                Self::Start(i) => {
                    if let Some(new_i) = i.checked_sub(count.saturating_div(2)) {
                        *self = Self::Start(new_i);
                        false
                    } else {
                        *self = Self::Start(usize::MIN);
                        true
                    }
                },
                Self::End(i) => {
                    if let Some(new_i) = i.checked_sub(count.saturating_div(2)) {
                        *self = Self::End(new_i);
                        false
                    } else {
                        *self = Self::End(usize::MIN);
                        true
                    }
                },
            }
        } else {
            match self {
                Self::Start(i) => {
                    if let Some(new_i) = i.checked_sub(count.saturating_div(2)) {
                        *self = Self::End(new_i);
                        false
                    } else {
                        *self = Self::End(usize::MIN);
                        true
                    }
                },
                Self::End(i) => {
                    if let Some(new_i) = i.checked_sub(count.saturating_div(2)) {
                        *self = Self::Start(new_i);
                        false
                    } else {
                        *self = Self::Start(usize::MIN);
                        true
                    }
                },
            }
        }
    }

    /// Increments the bound position
    /// 
    /// Returns whether the position has hit its maximum
    pub fn next_bound(&mut self) -> bool {
        self.advance_by(1)
    }

    /// Decrements the bound position
    /// 
    /// Returns whether the position has hit its minimum
    pub fn next_back_bound(&mut self) -> bool {
        self.advance_back_by(1)
    }
}

/// Iterator for bounds of [`AbsoluteBounds`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AbsoluteBoundsIter<'a> {
    bounds: Vec<&'a AbsoluteBounds>,
    position: BoundPosition,
}

impl Iterator for AbsoluteBoundsIter<'_> {
    type Item = AbsoluteBound;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position.next_bound() {
            return None;
        }
        
        self.position.get_abs_bound(&self.bounds)
    }
}

impl DoubleEndedIterator for AbsoluteBoundsIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.position.next_back_bound() {
            return None;
        }

        self.position.get_abs_bound(&self.bounds)
    }
}

/// Iterator for bounds of [`RelativeBounds`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelativeBoundsIter<'a> {
    bounds: Vec<&'a RelativeBounds>,
    position: BoundPosition,
}

impl Iterator for RelativeBoundsIter<'_> {
    type Item = RelativeBound;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position.next_bound() {
            return None;
        }
        
        self.position.get_rel_bound(&self.bounds)
    }
}

impl DoubleEndedIterator for RelativeBoundsIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.position.next_back_bound() {
            return None;
        }
        
        self.position.get_rel_bound(&self.bounds)
    }
}

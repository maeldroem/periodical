//! Set operations iterators created from [layered bounds iterators](crate::collections::intervals::layered_bounds)

pub mod diff;
pub mod intersect;
// pub mod sym_diff;
pub mod unite;

#[cfg(test)]
mod diff_tests;
#[cfg(test)]
mod intersect_tests;
#[cfg(test)]
mod unite_tests;

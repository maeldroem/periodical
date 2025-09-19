//! Interval iterators
//!
//! This module contains various iterators to deal with intervals. With those iterators, you can...
//!
//! - [Retrieve bounds from intervals](bounds)
//! - [Unite bounds](united_bounds)
//! - [Layering bounds to track active layers](layered_bounds)
//! - [Operate set operations on layered bounds](layered_bounds_set_ops)
//! - [Operate set operations on intervals](set_ops)
//! - [Retrieve the complements of intervals](complement)
//! - [Remove empty intervals from a collection](remove_empty)
//!
//! Most iterators have a public `new` method, but most of them come with input requirements.
//! Make sure your input meet those requirements.

pub mod bounds;
pub mod complement;
pub mod layered_bounds;
pub mod layered_bounds_set_ops;
pub mod remove_empty;
pub mod set_ops;
pub mod united_bounds;

#[cfg(test)]
mod bounds_tests;
#[cfg(test)]
mod complement_tests;
#[cfg(test)]
mod layered_bounds_tests;
#[cfg(test)]
mod remove_empty_tests;
#[cfg(test)]
mod united_bounds_tests;

// NOTE: collections can be improved by making them parallel with the rayon crate

/*
If we want to implement an operation "dispatcher" for multiple types, since we can easily run in the problem that
we can't do

impl<T: Iterator<Item = A>> CustomOperatorIter for T {}
impl<T: Iterator<Item = B>> CustomOperatorIter for T {}

as both have the signature `impl CustomOperatorIter for T` (associated type "Item" doesn't count),
we get a "conflicting implementations" error.

the solution is to do something like this:

struct Foo(u8);
struct Bar(u8);

trait CustomOperable {
    type Output: CustomOperable;
    fn custom_op(&self) -> Self::Output;
}

impl<T> CustomOperable for &T
where
    T: CustomOperable
{
    type Output = T::Output;
    fn custom_op(&self) -> Self::Output {
        (**self).custom_op()
    }
}

impl CustomOperable for Foo {
    type Output = Self;
    fn custom_op(&self) -> Self::Output {
        Self(self.0.saturating_add(1))
    }
}

impl CustomOperable for Bar {
    type Output = Self;
    fn custom_op(&self) -> Self::Output {
        Self(self.0.saturating_add(2))
    }
}

struct CustomIter<I> {
    iter: I,
}

impl<I> CustomIter<I> {
    fn new(iter: I) -> Self {
        CustomIter {
            iter,
        }
    }
}

impl<I> Iterator for CustomIter<I>
where
    I: Iterator,
    I::Item: CustomOperable<Output = I::Item>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.iter.next()?.custom_op())
    }
}

trait CustomIterDispatch: Iterator + Sized {
    fn custom_iter(self) -> CustomIter<Self> {
        CustomIter::new(self)
    }
}

impl<I> CustomIterDispatch for I
where
    I: Iterator,
    I::Item: CustomOperable<Output = I::Item>,
{}

Note: `where T: Iterator, T::Item: Operable` can also be written as `where T: Iterator<Item: Operable>`

In the future, implementing Iterator on a type that has non-overlapping trait bounds on its generics
will be allowed (see https://github.com/rust-lang/rust/issues/20400, emulation: https://github.com/rust-lang/rfcs/pull/1672#issuecomment-1405377983).
When this kind of implementations become standard, this crate should adopt it.
*/

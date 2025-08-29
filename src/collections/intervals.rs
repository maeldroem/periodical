//! Interval iterators

pub mod bounds;
pub mod complement;
pub mod layered_bounds;
pub mod precision;
pub mod relativity_conversion;
pub mod remove_empty;
pub mod set_ops;
pub mod united_bounds;
pub mod united_set;

#[cfg(test)]
mod complement_tests;
#[cfg(test)]
mod precision_tests;
#[cfg(test)]
mod relativity_conversion_tests;
#[cfg(test)]
mod remove_empty_tests;

// NOTE: Most of the operations in this file can be MAJORLY IMPROVED in terms of performance
// Suggestions for improvement:
// - Most operations can be done in parallel, but that would require them to be eagerly-evaluated, therefore it would
//   put into question whether we still need those methods as iterators. Or perhaps we can keep the iterators but
//   create methods that explicitly allow this eager evaluation?
// - Operations that "merges" two iterators may benefit from a point system: we merge all interval points into one list
//   and read from this list, therefore when we encounter a point that comes from the second iterator, we can apply
//   the operation and continue from there instead of checking for overlap of all elements of the first iter upon
//   each element of the second iter. This strategy is applicable to iterators but requires both sets of intervals
//   to be sorted chronologically.
// Current opinion: Such eager and constrained methods should be implemented on the IntervalIterator trait,
// that way, the caller can choose which one fits his needs: if they want to unite elements progressively of a list
// that is unsorted or sorted non-chronologically, they can choose to use the Union iterator. But if they need
// a fast way of uniting a list of intervals that is sorted chronologically, then they can call such methods.

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

use crate::collections::Intervals;
use crate::intervals::Interval;

/// New-type indicating that the contained iterator has to be united
pub struct Union<T>(T);

impl Union<Intervals> {
    /// Compacts the union of intervals by uniting intersecting intervals
    #[must_use]
    pub fn compact_intervals(self) -> Self {
        let iter = self.0.into_iter();
        let size_hint = iter.size_hint();

        let iter = iter
            .fold(
                Vec::with_capacity(size_hint.1.unwrap_or(size_hint.0)),
                |mut acc: Vec<Interval>, x| {
                    let last_interval = acc.last();

                    if last_interval.is_none() || todo!("last_interval doesn't intersect with x") {
                        acc.push(x);
                        return acc;
                    }

                    // safe unwrap because checked for None variant above
                    let last_interval = last_interval.unwrap();

                    let union = todo!("unite last_interval with x");
                    acc.insert(acc.len() - 1, union);
                    acc
                },
            )
            .into_iter()
            .collect::<Intervals>();

        Self::new(iter)
    }
}

impl<T> Union<T> {
    /// Unwraps the union type into the underlying iterator
    #[must_use]
    pub fn unwrap_iterator(self) -> T {
        self.0
    }

    /// Returns a reference to the underlying iterator
    #[must_use]
    pub fn iterator(&self) -> &T {
        &self.0
    }
}

impl<T> Union<T>
where
    T: Iterator,
{
    /// Creates a new union
    #[must_use]
    pub fn new(iter: T) -> Self {
        Union(iter)
    }
}

impl<T> Iterator for Union<T>
where
    T: Iterator,
{
    type Item = T::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

fn try_uniting_intervals(a: Interval, b: Interval) -> Result<Interval, ()> {
    Err(())
}

/// New-type indicating that the contained iterator has to be intersected
pub struct Intersection<T>(T);

impl<T> Intersection<T> {
    /// Unwraps the intersection type into the underlying iterator
    #[must_use]
    pub fn unwrap_iterator(self) -> T {
        self.0
    }

    /// Returns a reference to the underlying iterator
    #[must_use]
    pub fn iterator(&self) -> &T {
        &self.0
    }
}

impl<T> Intersection<T>
where
    T: Iterator,
{
    /// Creates a new intersection
    #[must_use]
    pub fn new(iter: T) -> Self {
        Intersection(iter)
    }
}

// impl<T> Iterator for Intersection<T>
// where
//     T: Iterator,
// {
//     type Item = T::Item;

//     fn next(&mut self) -> Option<Union<Self::Item>> {
//         todo!()
//     }
// }

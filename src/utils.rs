/// Applies `#[cfg(test)]` to a list of items
/// 
/// # Examples
/// 
/// ```ignore
/// tests! {
///     mod a_tests;
///     mod b_tests;
///     mod c_tests;
/// }
/// 
/// // Is equivalent to
/// 
/// #[cfg(test)]
/// mod a_tests;
/// #[cfg(test)]
/// mod b_tests;
/// #[cfg(test)]
/// mod c_tests;
/// ```
macro_rules! tests {
    ($($item:item)+) => {
        $(
            #[cfg(test)]
            $item
        )+
    };
}

// Path-based macro exports
pub(crate) use tests;

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

/// Applies [`#[doc(inline)]`][doc_inline_ref] to a list of items
/// 
/// # Examples
/// 
/// ```ignore
/// inline_docs! {
///     pub use submod::{StructX, StructY};
///     pub use othermod::even_lower::my_mod;
/// }
/// 
/// // Is equivalent to
/// 
/// #[doc(inline)]
/// pub use submod::{StructX, StructY};
/// #[doc(inline)]
/// pub use othermod::even_lower::my_mod;
/// ```
/// 
/// [doc_inline_ref]: https://doc.rust-lang.org/rustdoc/write-documentation/the-doc-attribute.html#inline-and-no_inline
macro_rules! inline_docs {
    ($($item:item)+) => {
        $(
            #[doc(inline)]
            $item
        )+
    };
}

// Path-based macro exports
pub(crate) use tests;
pub(crate) use inline_docs;

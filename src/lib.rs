#![warn(missing_docs)]
//! Generic heterogeneous array manipulation.
//!
//! This library attempts to mitigate the lack of variadic generics in rust
//!
//! Most of the available features are documented in the [`hlist`] module

pub mod hcons;
pub mod hlist;
pub mod tuple;

/// crate seal of approval
pub(crate) mod seal {
    /// this type is a tuple
    /// trait only implementable in this crate
    pub trait Tuple {}
}

/// Identifier for tuple types
///
/// Usefull with generics to require tuples as input parameters
///
/// this trait is sealed and implemented by this library only
///
/// analog to <https://dev-doc.rust-lang.org/nightly/std/marker/trait.Tuple.html>
pub trait Tuple: seal::Tuple {}

/// public definition of a tuple
/// usefull if one wants to require tuple only
impl<T: seal::Tuple> Tuple for T {}

/// Helper macro that counts the number of tokens passed to it.
///
/// # Examples
///
/// ```
/// # use tuplify::*;
/// assert_eq!(count_tokens![a b c], 3);
/// assert_eq!(count_tokens![], 0);
/// ```
#[macro_export]
macro_rules! count_tokens {
    () => { 0 };
    ($_:tt $($tail:tt) *) => { 1 + count_tokens![$($tail) *] };
}

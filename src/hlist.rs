//! Traits and generics implementations for heterogeneous lists.

use crate::{count_tokens, hcons::HEmpty, hcons_pat};

/// Heterogenous fixed size (aka: compile time) list.
pub trait HList {
    /// Number of elements in this list.
    const LEN: usize;

    /// Returns the number of elements in this list.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// assert_eq!(hcons![].len(), 0);
    /// assert_eq!(hcons![1].len(), 1);
    /// assert_eq!(hcons![1, true, "hello"].len(), 3);
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// assert_eq!(().len(), 0);
    /// assert_eq!((1,).len(), 1);
    /// assert_eq!((1, true, "hello").len(), 3);
    /// ```
    fn len(&self) -> usize { Self::LEN }

    /// Returns `true` if this list is empty (contains no elements).
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// assert!(hcons![].is_empty());
    /// assert!(!hcons![1].is_empty());
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// assert!(().is_empty());
    /// assert!(!(1,).is_empty());
    /// ```
    fn is_empty(&self) -> bool { Self::LEN == 0 }
}

/// Turns a reference to an heterogenous list into a list of references.
///
/// aka: &("some", "words") into: (&"some", "words")
///
/// Usefull for destructuring
pub trait AsRefs<'a>: HList {
    /// The type of the resulting list.
    type Output: HList + 'a;

    /// Gets immutable references over inner list elements.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let list = hcons![0, '1', "2"];
    ///
    /// assert_eq!(list.as_refs(), hcons![&0, &'1', &"2"]);
    /// assert_eq!(hcons![].as_refs(), hcons![]);
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let list = (0, '1', "2");
    ///
    /// assert_eq!(list.as_refs(), (&0, &'1', &"2"));
    /// assert_eq!(().as_refs(), ());
    /// ```
    ///
    /// ```
    /// use tuplify::*;
    /// fn need_refs(s: &str, s2: &str) {
    ///     //...
    /// }
    ///
    /// let x = (10, "foo", "bar");
    /// {
    ///     let x = x.as_refs();
    ///     need_refs(x.1, x.2);
    /// }
    /// ```
    fn as_refs(&'a self) -> Self::Output;
}

/// Turns a mutable reference into an heterogeneous list of mutable references.
pub trait AsMuts<'a>: HList {
    /// The type of the resulting list.
    type Output: HList + 'a;

    /// Gets mutable references over inner list elements.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let mut list = hcons![0, '1', "2"];
    ///
    /// assert_eq!(list.as_muts(), hcons![&mut 0, &mut '1', &mut "2"]);
    /// assert_eq!(hcons![].as_muts(), hcons![]);
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let mut list = (0, '1', "2");
    ///
    /// assert_eq!(list.as_muts(), (&mut 0, &mut '1', &mut "2"));
    /// assert_eq!(().as_muts(), ());
    /// ```
    fn as_muts(&'a mut self) -> Self::Output;
}

/// Concatenate 2 heterogenous lists, extending self with `Other`
///
/// ie: `(A, B).extend((C, D)) -> (A, B, C, D)`
pub trait Extend<Other: HList>: HList {
    /// The type of the resulting list.
    type Output: HList;

    /// Concatenates `self` and `other` by pre-pending every element of `self` to `other`.
    ///
    /// The resulting list is the same as `other` if `self` is empty.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let list = hcons![0, '1', "2"];
    /// let list = list.extend(hcons![4.0, 5i8, 6u8]);
    ///
    /// assert_eq!(list, hcons![0, '1', "2", 4.0, 5i8, 6u8]);
    /// ```
    /// does not work with single elements
    ///
    /// ```compile_fail
    /// use tuplify::*;
    /// let list = hcons![0, '1', "2"].extend(10);
    ///
    /// assert_eq!(list, (0, '1', "2", 10));
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let list = (0, '1', "2");
    /// let list = list.extend((4.0, 5i8, 6u8));
    ///
    /// assert_eq!(list, (0, '1', "2", 4.0, 5i8, 6u8));
    /// ```
    ///
    /// ```compile_fail
    /// use tuplify::*;
    /// let list = (0, '1', "2").extend(10);
    ///
    /// assert_eq!(list, (0, '1', "2", 10));
    /// ```
    ///
    /// ## Conversions
    ///
    /// Because this algorithm works by pre-pending elements at the beginning of `other`, this method can be used to convert
    /// between heterogeneous list types.
    ///
    /// ### [`crate::Tuple`] to [`crate::hcons::HCons`]
    ///
    /// ```
    /// use tuplify::*;
    /// let list = (0, '1', "2").extend(HEmpty);
    ///
    /// assert_eq!(list, hcons![0, '1', "2"]);
    /// ```
    ///
    /// ```
    /// use tuplify::*;
    /// let list = (0, '1', "2").extend(hcons![0, 1, 2]);
    ///
    /// assert_eq!(list, hcons![0, '1', "2", 0, 1, 2]);
    /// ```
    ///
    /// ### [`crate::hcons::HCons`] to [`crate::Tuple`]
    ///
    /// ```
    /// use tuplify::*;
    /// let list = hcons![0, '1', "2"].extend(());
    ///
    /// assert_eq!(list, (0, '1', "2"));
    /// ```
    /// ```
    /// use tuplify::*;
    /// let list = hcons![0, '1', "2"].extend((0, 1, 2));
    ///
    /// assert_eq!(list, (0, '1', "2", 0, 1, 2));
    /// ```
    fn extend(self, other: Other) -> Self::Output;
}

/// Helper trait to use heterogenous lists as arguments for [`Fn`]s.
///
/// TODO: remove or keep depending on <https://github.com/rust-lang/rust/issues/29625>
pub trait Fun<T: HList>: FunMut<T> {
    /// Calls `self` using the elements of the given list as arguments.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let list = hcons![0, '1', "2"];
    /// let value = 3u8;
    /// let func = |x: i32, y: char, z: &str| format!("{x} {y} {z} {value}");
    ///
    /// assert_eq!(&func.call_fun(list), "0 1 2 3");
    /// assert_eq!({ || 4 }.call_fun(HEmpty), 4);
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let list = (0, '1', "2");
    /// let value = 3u8;
    /// let func = |x: i32, y: char, z: &str| format!("{x} {y} {z} {value}");
    ///
    /// assert_eq!(&func.call_fun(list), "0 1 2 3");
    /// assert_eq!({ || 4 }.call_fun(()), 4);
    /// ```
    ///
    /// with fns
    /// ```
    /// use tuplify::*;
    /// fn le_fun() -> i32 { 42 }
    /// assert_eq!(42, le_fun.call_fun(()));
    /// fn more_fun(x: &str) -> String { format!("{x} 42") }
    /// let foo = ("The answer",);
    /// assert_eq!(String::from("The answer 42"), more_fun.call_fun(foo));
    /// fn even_more_fun(x: &String, y: &String, z: &i32) -> String { format!("{x} {y} {z}") }
    /// let foo = (String::from("The answer"), String::from("is"), 42);
    /// assert_eq!(String::from("The answer is 42"), even_more_fun.call_fun(foo.as_refs()));
    /// ```
    fn call_fun(&self, args: T) -> Self::Output;
}

/// Helper trait to use heterogenous lists as arguments for [`FnMut`]s.
///
/// TODO: remove or keep depending on <https://github.com/rust-lang/rust/issues/29625>
pub trait FunMut<T: HList>: FunOnce<T> {
    /// Calls `self` using the elements of the given list as arguments.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let list = hcons![0, '1', "2"];
    /// let mut value = String::new();
    /// let mut func = |x: i32, y: char, z: &str| value = format!("{x} {y} {z}");
    ///
    /// func.call_fun_mut(list);
    /// assert_eq!(&value, "0 1 2");
    /// ```
    ///
    /// Also works on functions taking no arguments:
    ///
    /// ```
    /// use tuplify::*;
    /// let mut value = String::new();
    /// let mut func = || value = "hello".to_string();
    ///
    /// func.call_fun_mut(HEmpty);
    /// assert_eq!(&value, "hello");
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let list = (0, '1', "2");
    /// let mut value = String::new();
    /// let mut func = |x: i32, y: char, z: &str| value = format!("{x} {y} {z}");
    ///
    /// func.call_fun_mut(list);
    /// assert_eq!(&value, "0 1 2");
    /// ```
    ///
    /// On a function taking no arguments:
    ///
    /// ```
    /// use tuplify::*;
    /// let mut value = String::new();
    /// let mut func = || value = "hello".to_string();
    ///
    /// func.call_fun_mut(());
    /// assert_eq!(&value, "hello");
    /// ```
    fn call_fun_mut(&mut self, args: T) -> Self::Output;
}

/// Helper trait to use heterogenous lists as arguments for [`FnOnce`]s.
///
/// TODO: remove or keep depending on <https://github.com/rust-lang/rust/issues/29625>
pub trait FunOnce<T: HList> {
    /// The return type of the function.
    type Output;

    /// Calls `self` using the elements of the given list as arguments.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let list = hcons![0, '1', "2"];
    /// let value = "hello".to_string();
    /// let func = |x: i32, y: char, z: &str| format!("{x} {y} {z}");
    ///
    /// assert_eq!(&func.call_fun_once(list), "0 1 2");
    /// ```
    ///
    /// Also works on functions taking no arguments:
    ///
    /// ```
    /// use tuplify::*;
    /// let value = "hello".to_string();
    ///
    /// assert_eq!(&{ move || value }.call_fun_once(HEmpty), "hello");
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let list = (0, '1', "2");
    /// let value = "hello".to_string();
    /// let func = move |x: i32, y: char, z: &str| format!("{value} {x} {y} {z}");
    ///
    /// assert_eq!(&func.call_fun_once(list), "hello 0 1 2");
    /// ```
    ///
    /// On a function taking no arguments:
    ///
    /// ```
    /// use tuplify::*;
    /// let value = "hello".to_string();
    /// assert_eq!(&{ move || value }.call_fun_once(()), "hello");
    /// ```
    fn call_fun_once(self, args: T) -> Self::Output;
}

/// Trait for wrapping each element of an heterogenous list in [`Some`].
pub trait IntoOpts: HList {
    /// The type of the resulting list.
    type Output: HList + Sized;

    /// Wraps all elements of an heterogeneous list in `Some`.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let list = hcons![0, '1', "2"];
    ///
    /// assert_eq!(list.into_opts(), hcons![Some(0), Some('1'), Some("2")]);
    /// assert_eq!(hcons![].into_opts(), hcons![]);
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let list = (0, '1', "2");
    ///
    /// assert_eq!(list.into_opts(), (Some(0), Some('1'), Some("2")));
    /// assert_eq!(().into_opts(), ());
    /// ```
    fn into_opts(self) -> Self::Output;
}

/// Adds an element at the begining of the list
///
/// Inverse of [`PushBack`]
pub trait PushFront<E>: HList {
    /// The type of the resulting list.
    type Output: HList;

    /// Pushes an element at the begining of the list.
    ///
    /// # Examples
    ///
    /// ## With `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let list = hcons!['1', "2"].push_front(0);
    ///
    /// assert_eq!(list, hcons![0, '1', "2"]);
    /// ```
    ///
    /// ## With tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let list = ('1', "2").push_front(0);
    ///
    /// assert_eq!(list, (0, '1', "2"));
    /// ```
    /// ```
    /// use tuplify::*;
    /// let list = ('1', "2").push_front((0, 1));
    ///
    /// assert_eq!(list, ((0, 1), '1', "2"));
    /// ```
    /// ```
    /// use tuplify::*;
    /// let list = ().push_front(1);
    ///
    /// assert_eq!(list, (1,));
    /// ```
    fn push_front(self, element: E) -> Self::Output;
}

/// Adds an element at the end of the list
///
/// Inverse of [`PushFront`]
pub trait PushBack<E>: HList {
    /// The type of the resulting list.
    type Output;

    /// Pushes an element at the end of the list.
    ///
    /// # Examples
    ///
    /// ## With `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let list = hcons!['1', "2"].push_back(0);
    ///
    /// assert_eq!(list, hcons!['1', "2", 0]);
    /// ```
    ///
    /// ## With tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let list = ('1', "2").push_back(0);
    ///
    /// assert_eq!(list, ('1', "2", 0));
    /// ```
    /// ```
    /// use tuplify::*;
    /// let list = ('1', "2").push_back((0, 1));
    ///
    /// assert_eq!(list, ('1', "2", (0, 1)));
    /// ```
    /// ```
    /// use tuplify::*;
    /// let list = ().push_back(1);
    ///
    /// assert_eq!(list, (1,));
    /// ```
    fn push_back(self, element: E) -> Self::Output;
}

/// Reversible heterogeneous list.
pub trait Reverse: HList {
    /// The type of the resulting list.
    type Output;

    /// Reverses this list.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// assert_eq!(hcons![].rev(), hcons![]);
    /// assert_eq!(hcons![1].rev(), hcons![1]);
    /// assert_eq!(hcons![0, '1', "2"].rev(), hcons!["2", '1', 0]);
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// assert_eq!(().rev(), ());
    /// assert_eq!((1,).rev(), (1,));
    /// assert_eq!((0, '1', "2").rev(), ("2", '1', 0));
    /// ```
    fn rev(self) -> Self::Output;
}

/// Removes the list front element
/// if the list is empty, returns None
pub trait TryUncons: HList + Sized {
    /// Type of the list front element
    type Head;

    /// Type of the list tail (remaining list after its front element removal).
    type Tail: HList;

    /// Pops an element at the begining of the list.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplify::*;
    ///
    /// assert_eq!(Ok((0, hcons!['1', "2"])), hcons![0, '1', "2"].try_uncons());
    /// assert_eq!(Ok((0, ('1', "2"))), (0, '1', "2").try_uncons());
    /// ```
    /// [`TryUncons::try_uncons`] works with empty lists
    /// ```
    /// use tuplify::*;
    /// assert_eq!(Err(()), ().try_uncons());
    /// assert_eq!(Err(hcons![]), hcons![].try_uncons());
    /// ```
    fn try_uncons(self) -> Result<(Self::Head, Self::Tail), Self>;
}

/// Try to convert a list of [`Some`]s to a list of the inner values.
///
/// In case of failure, returns `self` as the error
///
/// See [`ValidateOpt`] if the original list is non needed
pub trait TryValidateOpt: HList + Sized {
    /// The type of the resulting list.
    type Output;

    /// Tries to convert this list of [`Some`]s to a list of the inner values.
    ///
    /// If any element is [`None`], returns `Err(Self)`.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let foo = hcons![Some(0), Some('1'), Some("2")].try_validate();
    /// let bar = hcons![Some(0), Option::<char>::None, Some("2")].try_validate();
    ///
    /// assert_eq!(foo, Ok(hcons![0, '1', "2"]));
    // / assert_eq!(bar, Err(hcons![Some(0), Option::<char>::None, Some("2")]));
    /// ```
    /// 
    /// ## On tuples
    /// ```
    /// use tuplify::*;
    /// let foo = (Some(0), Some('1'), Some("2")).try_validate();
    /// let bar = (Some(0), Option::<char>::None, Some("2")).try_validate();
    ///
    /// assert_eq!(foo, Ok((0, '1', "2")));
    /// assert_eq!(bar, Err((Some(0), Option::<char>::None, Some("2"))));
    /// ```
    fn try_validate(self) -> Result<Self::Output, Self>;
}

/// Trait used for the conversion of a list of `Ok`s to a list of the inner values.
///
/// See [`ValidateRes`] if the original list is non needed
pub trait TryValidateRes: HList + Sized {
    /// The type of the resulting list.
    type Output;

    /// Tries to convert this list of `Ok`s to a list of the inner values.
    /// If any element is `Err`, returns `Err(Self)`.
    ///
    /// Note: because errors are discarded, `Result`s don't have to have the same error type.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let foo = hcons![
    ///     Result::<_, i8>::Ok(0),
    ///     Result::<_, u32>::Ok('1'),
    ///     Result::<_, f64>::Ok("2")
    /// ]
    /// .try_validate();
    /// let bar = hcons![
    ///     Result::<_, u8>::Ok(0),
    ///     Result::<i8, _>::Err("bad"),
    ///     Result::<_, u8>::Ok("2")
    /// ]
    /// .try_validate();
    ///
    /// assert_eq!(foo, Ok(hcons![0, '1', "2"]));
    /// assert_eq!(bar, Err(hcons![Ok(0), Err("bad"), Ok("2")]));
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let foo =
    ///     (Result::<_, i8>::Ok(0), Result::<_, u32>::Ok('1'), Result::<_, f64>::Ok("2"))
    ///         .try_validate();
    /// let bar =
    ///     (Result::<_, u8>::Ok(0), Result::<i8, _>::Err("bad"), Result::<_, u8>::Ok("2"))
    ///         .try_validate();
    ///
    /// assert_eq!(foo, Ok((0, '1', "2")));
    /// assert_eq!(bar, Err((Ok(0), Err("bad"), Ok("2"))));
    /// ```
    fn try_validate(self) -> Result<Self::Output, Self>;
}

/// Removes the list front element
pub trait Uncons: HList {
    /// Type of the list front element
    type Head;

    /// Type of the list tail
    type Tail: HList;

    /// Pops an element from the list head.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let (head, tail) = hcons![0, '1', "2"].uncons();
    ///
    /// assert_eq!(head, 0);
    /// assert_eq!(tail, hcons!['1', "2"]);
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let (head, tail) = (0, '1', "2").uncons();
    ///
    /// assert_eq!(head, 0);
    /// assert_eq!(tail, ('1', "2"));
    /// ```
    /// [`Uncons::uncons`] not work with empty lists
    /// ```compile_fail
    /// use tuplify::*;
    /// let foo = ().uncons();
    /// let foo = hcons![].uncons();
    /// ```
    /// see: [`UnconsOpt`] to work with empty lists.
    ///
    /// If the list contains 1 element, then the tail is empty
    /// ```
    /// use tuplify::*;
    /// assert_eq!((10, HEmpty), hcons![10].uncons());
    /// assert_eq!((10, ()), (10,).uncons());
    /// ```
    fn uncons(self) -> (Self::Head, Self::Tail);
}

/// Extension trait for types implementing [`Uncons`].
pub trait UnconsExt: Uncons {
    /// Returns the list front element.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let list = hcons![0, '1', "2"];
    ///
    /// assert_eq!(list.into_head(), 0);
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let list = (0, '1', "2");
    ///
    /// assert_eq!(list.into_head(), 0);
    /// ```
    fn into_head(self) -> Self::Head;

    /// Returns the list tail
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let list = hcons![0, '1', "2"];
    ///
    /// assert_eq!(list.into_tail(), hcons!['1', "2"]);
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let list = (0, '1', "2");
    ///
    /// assert_eq!(list.into_tail(), ('1', "2"));
    /// ```
    fn into_tail(self) -> Self::Tail;
}

/// Removes the list front element.
///
/// if the list is empty, returns None
pub trait UnconsOpt: HList {
    /// Type of the list front element
    type Head;

    /// Type of the list tail
    type Tail: HList;

    /// ```
    /// use tuplify::*;
    ///
    /// assert_eq!(Some((0, hcons!['1', "2"])), hcons![0, '1', "2"].uncons_opt());
    /// assert_eq!(Some((0, ('1', "2"))), (0, '1', "2").uncons_opt());
    /// ```
    /// [`UnconsOpt::uncons_opt`] works with empty lists
    /// ```
    /// use tuplify::*;
    /// assert_eq!(None, ().uncons_opt());
    /// assert_eq!(None, hcons![].uncons_opt());
    /// ```
    fn uncons_opt(self) -> Option<(Self::Head, Self::Tail)>;
}

/// Unpacks heterogeneous lists containing exactly one element.
///
/// If the list has only one item, returns the item.
///
/// This is usefull when combining tuples and function signatures
pub trait Unpack: HList {
    /// The type of the unpacked element, or `Self` if the list does not contain one element.
    type Output;

    /// Unpacks this list into its single element.
    ///
    /// if the list does not contain one element, returns `Self`.
    /// Example:
    /// ```
    /// use tuplify::*;
    ///
    /// fn do_something<T: Unpack>(t: T) -> Option<T::Output> { Some(t.unpack()) }
    ///
    /// assert_eq!(Some("hello"), do_something(("hello",)));
    /// assert_eq!(Some(("I", "am", "tuple")), do_something(("I", "am", "tuple")));
    /// assert_eq!(Some("hello"), do_something(hcons!("hello",)));
    /// assert_eq!(
    ///     Some(hcons!("I", "am", "HCons")),
    ///     do_something(hcons!("I", "am", "HCons"))
    /// );
    /// ```
    fn unpack(self) -> Self::Output;
}

/// Convert a list of [`Option`]s to an option of the inner elements.
///
/// If one of the list elements is [`None`], returns [`None`]
///
/// See [`TryValidateOpt`] if the original list should be kept
pub trait ValidateOpt: HList {
    /// The type of the resulting list.
    type Output;

    /// Converts this list of `Some`s to a list of the inner values.
    ///
    /// If any element is `None`, returns `None`.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let foo = hcons![Some(0), Some('1'), Some("2")].validate();
    /// let bar = hcons![Some(0), Option::<char>::None, Some("2")].validate();
    ///
    /// assert_eq!(foo, Some(hcons![0, '1', "2"]));
    /// assert_eq!(bar, None);
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let foo = (Some(0), Some('1'), Some("2")).validate();
    /// let bar = (Some(0), Option::<char>::None, Some("2")).validate();
    ///
    /// assert_eq!(foo, Some((0, '1', "2")));
    /// assert_eq!(bar, None);
    /// ```
    fn validate(self) -> Option<Self::Output>;
}

/// Convert a list of [`Result`]s to an option of the inner elements.
///
/// If one of the list elements is [`Err`], returns the error.
///
/// See [`TryValidateRes`] if the original list should be kept
///
/// TODO: see if generic error should be moved to type in the trait
pub trait ValidateRes<E>: HList {
    /// The type of the resulting list.
    type Output;

    /// Converts this list of `Ok`s to a list of the inner values. All `Result`s must have the same error type.
    ///
    /// If any element is `Err`, returns the `Err`.
    ///
    /// # Examples
    ///
    /// ## On `HCons`
    ///
    /// ```
    /// use tuplify::*;
    /// let foo: Result<_, ()> = hcons![Ok(0), Ok('1'), Ok("2")].validate();
    /// let bar = hcons![Ok(0), Result::<char, _>::Err("bad"), Ok("2")].validate();
    ///
    /// assert_eq!(foo, Ok(hcons![0, '1', "2"]));
    /// assert_eq!(bar, Err("bad"));
    /// ```
    ///
    /// ## On tuples
    ///
    /// ```
    /// use tuplify::*;
    /// let foo: Result<_, ()> = (Ok(0), Ok('1'), Ok("2")).validate();
    /// let bar = (Ok(0), Result::<char, _>::Err("bad"), Ok("2")).validate();
    ///
    /// assert_eq!(foo, Ok((0, '1', "2")));
    /// assert_eq!(bar, Err("bad"));
    /// ```
    fn validate(self) -> Result<Self::Output, E>;
}

/// Removes the element at the back of the list
pub trait PopBack {
    /// Last element of the list
    type Back;
    /// Elements of the list without the last one
    type Front: HList;

    /// removes the last element of the list
    ///
    /// returns the last element of the list and the remaining list
    ///
    /// Example:
    /// ```
    /// use tuplify::*;
    ///
    /// assert_eq!((1, 2, 3).pop_back(), (3, (1, 2)));
    /// assert_eq!(hcons!(1, 2, 3).pop_back(), (3, hcons!(1, 2)));
    /// assert_eq!((1, 2).pop_back(), (2, (1,)));
    /// assert_eq!(hcons!(1, 2).pop_back(), (2, hcons!(1)));
    /// assert_eq!((1,).pop_back(), (1, ()));
    /// assert_eq!(hcons!(1).pop_back(), (1, HEmpty));
    /// ```
    ///
    /// Does not work on emty lists
    ///
    /// ```compile_fail
    /// use tuplify::*;
    ///
    /// assert_eq!(().pop_back(), ());
    /// assert_eq!(hcons!().pop_back(), (HEmpty, HEmpty));
    /// ```
    fn pop_back(self) -> (Self::Back, Self::Front);
}

/// Removes the element at the back of the list
pub trait TryPopBack {
    /// Last element of the list
    type Back;
    /// Elements of the list without the last one
    type Front: HList;

    /// removes the last element of the list
    ///
    /// returns the last element of the list and the remaining list, None if empty
    ///
    /// Example:
    /// ```
    /// use tuplify::*;
    ///
    /// assert_eq!((1, 2, 3).try_pop_back(), Some((3, (1, 2))));
    /// assert_eq!(hcons!(1, 2, 3).try_pop_back(), Some((3, hcons!(1, 2))));
    /// assert_eq!((1, 2).try_pop_back(), Some((2, (1,))));
    /// assert_eq!(hcons!(1, 2).try_pop_back(), Some((2, hcons!(1))));
    /// assert_eq!((1,).try_pop_back(), Some((1, ())));
    /// assert_eq!(hcons!(1).try_pop_back(), Some((1, HEmpty)));
    /// ```
    ///
    /// Works on emty lists
    ///
    /// ```
    /// use tuplify::*;
    ///
    /// assert_eq!(().try_pop_back(), None);
    /// assert_eq!(hcons!().try_pop_back(), None);
    /// ```
    fn try_pop_back(self) -> Option<(Self::Back, Self::Front)>;
}

/// Removes the element at the back of the list
pub trait PopBackExt {
    /// Last element of the list
    type Back;
    /// Elements of the list without the last one
    type Front: HList;

    /// transforms self into the last element
    ///
    /// Example:
    /// ```
    /// use tuplify::*;
    ///
    /// assert_eq!((1, 2, 3).into_back(), 3);
    /// assert_eq!(hcons!(1, 2, 3).into_back(), 3);
    /// assert_eq!((1, 2).into_back(), 2);
    /// assert_eq!(hcons!(1, 2).into_back(), 2);
    /// assert_eq!((1,).into_back(), 1);
    /// assert_eq!(hcons!(1).into_back(), 1);
    /// ```
    ///
    /// Does not work on emty lists
    ///
    /// ```compile_fail
    /// use tuplify::*;
    ///
    /// assert_eq!(().into_back(), ());
    /// assert_eq!(hcons!().into_back(), (HEmpty, HEmpty));
    /// ```
    fn into_back(self) -> Self::Back;
    /// transforms self into a list without the last element
    ///
    /// Example:
    /// ```
    /// use tuplify::*;
    ///
    /// assert_eq!((1, 2, 3).into_heads(), (1, 2));
    /// assert_eq!(hcons!(1, 2, 3).into_heads(), hcons!(1, 2));
    /// assert_eq!((1, 2).into_heads(), (1,));
    /// assert_eq!(hcons!(1, 2).into_heads(), hcons!(1));
    /// assert_eq!((1,).into_heads(), ());
    /// assert_eq!(hcons!(1).into_heads(), HEmpty);
    /// ```
    ///
    /// Does not work on emty lists
    ///
    /// ```compile_fail
    /// use tuplify::*;
    ///
    /// assert_eq!(().into_heads(), ());
    /// assert_eq!(hcons!().into_heads(), (HEmpty, HEmpty));
    /// ```
    fn into_heads(self) -> Self::Front;
}

/// a type that can never be instantiated
///
/// TODO: remove and replace with <https://github.com/rust-lang/rust/issues/35121> once stabilized or behind a flag
#[derive(Debug, PartialEq, Eq)]
pub enum Never {}

/// the never list
///
/// TODO: remove and replace with <https://github.com/rust-lang/rust/issues/35121> once stabilized or behind a flag
#[derive(Debug, PartialEq, Eq)]
pub enum NeverList {}

impl<Dst, Src> Extend<Dst> for Src
where
    Src: Uncons,
    Dst: HList,
    Src::Tail: Extend<Dst>,
    <Src::Tail as Extend<Dst>>::Output: PushFront<Src::Head>,
{
    type Output = <<Src::Tail as Extend<Dst>>::Output as PushFront<Src::Head>>::Output;

    fn extend(self, other: Dst) -> Self::Output {
        let (h, t) = self.uncons();
        t.extend(other).push_front(h)
    }
}

impl<L> IntoOpts for L
where
    L: Uncons,
    L::Tail: IntoOpts,
    <L::Tail as IntoOpts>::Output: PushFront<Option<L::Head>>,
{
    type Output = <<L::Tail as IntoOpts>::Output as PushFront<Option<L::Head>>>::Output;

    fn into_opts(self) -> Self::Output {
        let (head, tail) = self.uncons();
        tail.into_opts().push_front(Some(head))
    }
}

impl<L, E> PushBack<E> for L
where
    L: Uncons,
    L::Tail: PushBack<E>,
    <L::Tail as PushBack<E>>::Output: PushFront<L::Head>,
{
    type Output = <<L::Tail as PushBack<E>>::Output as PushFront<L::Head>>::Output;

    fn push_back(self, element: E) -> Self::Output {
        let (h, t) = self.uncons();
        t.push_back(element).push_front(h)
    }
}

impl<L> Reverse for L
where
    L: Uncons,
    L::Tail: Reverse,
    <L::Tail as Reverse>::Output: PushBack<L::Head>,
{
    type Output = <<L::Tail as Reverse>::Output as PushBack<L::Head>>::Output;

    fn rev(self) -> Self::Output {
        let (h, t) = self.uncons();
        t.rev().push_back(h)
    }
}

// Conversions From/To arrays
macro_rules! impl_from_into_array {
    () => {};
    ($head:ident $($tail:ident) *) => {
        impl_from_into_array!($($tail) *);
        impl<E, $head: Into<E>, $($tail: Into<E>), *> From<crate::HCons![$head, $($tail,) *]> for [E; { count_tokens!($head $($tail) *)}] {
            #[allow(non_snake_case)]
            fn from(value: crate::HCons![$head, $($tail,) *]) -> [E; crate::count_tokens!($head $($tail) *)] {
                let hcons_pat!($head, $($tail,) *) = value;
                [$head.into(), $($tail.into(),) *]
            }
        }

        impl<E, $head, $($tail), *> From<[E; { count_tokens!($head $($tail) *)}]> for crate::HCons![$head, $($tail,) *]
        where E: Into<$head> $(+ Into<$tail>) *
        {
            #[allow(non_snake_case)]
            fn from(arr: [E; crate::count_tokens!($head $($tail) *)]) -> Self {
                let [$head, $($tail,) *] = arr;
                crate::hcons!($head.into(), $($tail.into(),) *)
            }
        }
    };
}

impl_from_into_array!(T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32);

impl<T> From<[T; 0]> for HEmpty {
    fn from(_: [T; 0]) -> HEmpty { HEmpty }
}

impl TryUncons for () {
    type Head = Never;
    type Tail = NeverList;

    fn try_uncons(self) -> Result<(Self::Head, Self::Tail), Self> { Err(self) }
}

impl TryUncons for HEmpty {
    type Head = Never;
    type Tail = NeverList;

    fn try_uncons(self) -> Result<(Self::Head, Self::Tail), Self> { Err(self) }
}

impl<T: Uncons> TryUncons for T {
    type Head = T::Head;
    type Tail = T::Tail;

    fn try_uncons(self) -> Result<(Self::Head, Self::Tail), Self> { Ok(self.uncons()) }
}

impl<T: Uncons> UnconsExt for T {
    fn into_head(self) -> Self::Head { self.uncons().0 }

    fn into_tail(self) -> Self::Tail { self.uncons().1 }
}

impl HList for NeverList {
    const LEN: usize = 0;
}

impl UnconsOpt for () {
    type Head = Never;
    type Tail = NeverList;

    fn uncons_opt(self) -> Option<(Self::Head, Self::Tail)> { None }
}

impl UnconsOpt for HEmpty {
    type Head = Never;
    type Tail = NeverList;

    fn uncons_opt(self) -> Option<(Self::Head, Self::Tail)> { None }
}

impl<T: Uncons> UnconsOpt for T {
    type Head = T::Head;
    type Tail = T::Tail;

    fn uncons_opt(self) -> Option<(Self::Head, Self::Tail)> { Some(self.uncons()) }
}

impl<L, H> ValidateOpt for L
where
    L: Uncons<Head = Option<H>>,
    L::Tail: ValidateOpt,
    <L::Tail as ValidateOpt>::Output: PushFront<H>,
{
    type Output = <<L::Tail as ValidateOpt>::Output as PushFront<H>>::Output;

    fn validate(self) -> Option<Self::Output> {
        let (head, tail) = self.uncons();
        head.and_then(|h| tail.validate().map(move |t| t.push_front(h)))
    }
}

impl<L, H, E> ValidateRes<E> for L
where
    L: Uncons<Head = Result<H, E>>,
    L::Tail: ValidateRes<E>,
    <L::Tail as ValidateRes<E>>::Output: PushFront<H>,
{
    type Output = <<L::Tail as ValidateRes<E>>::Output as PushFront<H>>::Output;

    fn validate(self) -> Result<Self::Output, E> {
        let (head, tail) = self.uncons();
        head.and_then(|h| tail.validate().map(move |t| t.push_front(h)))
    }
}

impl<L, H> TryValidateOpt for L
where
    L: Uncons<Head = Option<H>>,
    L::Tail: TryValidateOpt + PushFront<L::Head, Output = L>,
    <L::Tail as TryValidateOpt>::Output: PushFront<H>,
{
    type Output = <<L::Tail as TryValidateOpt>::Output as PushFront<H>>::Output;

    fn try_validate(self) -> Result<Self::Output, Self> {
        let (head, tail) = self.uncons();

        match head {
            Some(h) => match tail.try_validate() {
                Ok(t) => Ok(t.push_front(h)),
                Err(t) => Err(t.push_front(Some(h))),
            },
            None => Err(tail.push_front(head)),
        }
    }
}

impl<L, H, E> TryValidateRes for L
where
    L: Uncons<Head = Result<H, E>>,
    L::Tail: TryValidateRes + PushFront<L::Head, Output = L>,
    <L::Tail as TryValidateRes>::Output: PushFront<H>,
{
    type Output = <<L::Tail as TryValidateRes>::Output as PushFront<H>>::Output;

    fn try_validate(self) -> Result<Self::Output, Self> {
        let (head, tail) = self.uncons();

        match head {
            Ok(h) => match tail.try_validate() {
                Ok(t) => Ok(t.push_front(h)),
                Err(t) => Err(t.push_front(Ok(h))),
            },
            _ => Err(tail.push_front(head)),
        }
    }
}

impl<L> PopBack for L
where
    L: Reverse,
    L::Output: Uncons,
    <L::Output as Uncons>::Tail: Reverse,
    <<L::Output as Uncons>::Tail as Reverse>::Output: HList,
{
    type Back = <L::Output as Uncons>::Head;
    type Front = <<L::Output as Uncons>::Tail as Reverse>::Output;

    fn pop_back(self) -> (Self::Back, Self::Front) {
        let (b, h) = self.rev().uncons();
        (b, h.rev())
    }
}

impl<L> TryPopBack for L
where
    L: PopBack,
{
    type Back = L::Back;
    type Front = L::Front;

    fn try_pop_back(self) -> Option<(Self::Back, Self::Front)> { Some(self.pop_back()) }
}

impl<L> PopBackExt for L
where
    L: PopBack,
{
    type Back = L::Back;
    type Front = L::Front;

    fn into_back(self) -> Self::Back { self.pop_back().0 }

    fn into_heads(self) -> Self::Front { self.pop_back().1 }
}

//! HList visitor module
use crate::{count_tokens, hcons, hcons_pat, HCons, HList};
/// Applies a function over all elements of the tuple
///
/// See also [VisitWith] for a shorthand call on [HList]s
///
/// This trait is automatically implemented on HLists where all elements implement the [Visit] trait
///
/// Example with tuples:
/// ```
/// # use tuplify::Visit;
/// # use tuplify::Visitor;
/// struct MyVisitor;
/// struct MyVisitor2;
///
/// impl Visit<MyVisitor> for usize {
///     type Output = Self;
///
///     fn visit_item(self, idx: usize) -> Self::Output {
///         assert_eq!(idx, 0);
///         self + 1
///     }
/// }
///
/// impl Visit<MyVisitor> for &mut String {
///     type Output = Self;
///
///     fn visit_item(self, idx: usize) -> Self::Output {
///         assert_eq!(idx, 1);
///         self.push_str("hello");
///         self
///     }
/// }
/// impl Visit<MyVisitor2> for usize {
///     type Output = Self;
///
///     fn visit_item(self, idx: usize) -> Self::Output { 1 }
/// }
///
/// impl Visit<MyVisitor2> for &mut String {
///     type Output = usize;
///
///     fn visit_item(self, idx: usize) -> Self::Output { 2 }
/// }
/// let tupl = (10usize, &mut String::from("foo"));
///
/// assert_eq!(MyVisitor::visit(tupl), (11, &mut String::from("foohello")));
/// assert_eq!(MyVisitor2::visit((10usize, &mut String::from("foo"))), (1, 2))
/// ```
///
/// Example with [struct@HCons]:
/// ```
/// # use tuplify::Visit;
/// # use tuplify::Visitor;
/// # use tuplify::hcons;
/// struct MyVisitor;
///
/// impl Visit<MyVisitor> for usize {
///     type Output = Self;
///
///     fn visit_item(self, idx: usize) -> Self::Output {
///         assert_eq!(idx, 0);
///         self + 1
///     }
/// }
///
/// impl Visit<MyVisitor> for &mut String {
///     type Output = Self;
///
///     fn visit_item(self, idx: usize) -> Self::Output {
///         assert_eq!(idx, 1);
///         self.push_str("hello");
///         self
///     }
/// }
/// let mut s = String::from("foo");
/// let tupl = hcons!(10usize, &mut s);
/// assert_eq!(MyVisitor::visit(tupl), hcons!(11, &mut String::from("foohello")));
/// ```
pub trait Visitor<T: HList> {
    /// Output list
    type Output: HList;

    /// calls [Visit] on every element
    fn visit(t: T) -> Self::Output;
}

/// Implementation of [Visitor] on [HList]s
///
/// This trait is automatically implemented when all elements implement the [Visit] trait
///
/// Example with tuples:
/// ```
/// # use tuplify::Visit;
/// # use tuplify::Visitor;
/// # use tuplify::VisitWith;
/// struct MyVisitor;
///
/// impl Visit<MyVisitor> for usize {
///     type Output = Self;
///
///     fn visit_item(self, idx: usize) -> Self::Output {
///         assert_eq!(idx, 0);
///         self + 1
///     }
/// }
///
/// impl Visit<MyVisitor> for &mut String {
///     type Output = Self;
///
///     fn visit_item(self, idx: usize) -> Self::Output {
///         assert_eq!(idx, 1);
///         self.push_str("hello");
///         self
///     }
/// }
///
/// let tupl = (10usize, &mut String::from("foo"));
/// assert_eq!(tupl.visit_with::<MyVisitor>(), (11, &mut String::from("foohello")));
/// ```
/// Example with [struct@HCons]:
/// ```
/// # use tuplify::Visit;
/// # use tuplify::Visitor;
/// # use tuplify::VisitWith;
/// # use tuplify::hcons;
/// struct MyVisitor;
///
/// impl Visit<MyVisitor> for usize {
///     type Output = Self;
///
///     fn visit_item(self, idx: usize) -> Self::Output {
///         assert_eq!(idx, 0);
///         self + 1
///     }
/// }
///
/// impl Visit<MyVisitor> for &mut String {
///     type Output = Self;
///
///     fn visit_item(self, idx: usize) -> Self::Output {
///         assert_eq!(idx, 1);
///         self.push_str("hello");
///         self
///     }
/// }
///
/// let mut s = String::from("foo");
/// let tupl = hcons!(10usize, &mut s);
/// assert_eq!(tupl.visit_with::<MyVisitor>(), hcons!(11, &mut String::from("foohello")));
/// ```
pub trait VisitWith: HList + Sized {
    /// maps the given [Visitor] `T` to this list
    fn visit_with<T>(self) -> <T as Visitor<Self>>::Output
    where
        T: Visitor<Self>;
}

impl<L: HList + Sized> VisitWith for L {
    fn visit_with<T>(self) -> <T as Visitor<Self>>::Output
    where
        T: Visitor<Self>,
    {
        T::visit(self)
    }
}

/// Bridge to map a function to a single tuple element
pub trait Visit<T> {
    /// result of the map function
    type Output;

    /// Callback with a tuple element and index
    fn visit_item(self, idx: usize) -> Self::Output;
}

/// Creates an iterator from a tuple and a visitor
///
/// This trait is automatically implemented on HLists where all elements implement the [Visit] trait
///
/// Example with tuples:
/// ```
/// # use tuplify::Visit;
/// # use tuplify::HListIntoIter;
/// # use tuplify::VisitWith;
/// struct MyMapper;
///
/// impl Visit<MyMapper> for usize {
///     type Output = String;
///
///     fn visit_item(self, idx: usize) -> Self::Output {
///         assert_eq!(idx, 0);
///         format!("{}", self + 1)
///     }
/// }
///
/// impl Visit<MyMapper> for &mut String {
///     type Output = String;
///
///     fn visit_item(self, idx: usize) -> Self::Output {
///         assert_eq!(idx, 1);
///         self.push_str("hello");
///         self.clone()
///     }
/// }
///
/// let tupl = (10usize, &mut String::from("foo"));
/// assert_eq!(
///     MyMapper::into_iter(tupl).collect::<Vec<_>>(),
///     vec![String::from("11"), String::from("foohello")]
/// );
/// ```
///
/// Example with [struct@HCons]:
/// ```
/// # use tuplify::Visit;
/// # use tuplify::HListIntoIter;
/// # use tuplify::VisitWith;
/// # use tuplify::hcons;
/// struct MyMapper;
///
/// impl Visit<MyMapper> for usize {
///     type Output = String;
///
///     fn visit_item(self, idx: usize) -> Self::Output {
///         assert_eq!(idx, 0);
///         format!("{}", self + 1)
///     }
/// }
///
/// impl Visit<MyMapper> for String {
///     type Output = String;
///
///     fn visit_item(self, idx: usize) -> Self::Output {
///         let mut s = self.clone();
///         s.push_str(&format!("{idx}"));
///         s
///     }
/// }
///
/// let tupl = hcons!(10usize, String::from("string-"), String::from("string-"));
/// assert_eq!(
///     MyMapper::into_iter(tupl).collect::<Vec<_>>(),
///     vec![String::from("11"), String::from("string-1"), String::from("string-2")]
/// );
/// ```
///
/// This could be used with [crate::AsRefs] or [crate::AsMuts]
///
/// ```rust
/// # use tuplify::Visit;
/// # use tuplify::HListIntoIter;
/// # use tuplify::VisitWith;
/// # use tuplify::AsRefs;
/// # use tuplify::hcons;
/// struct MyMapper;
///
/// impl Visit<MyMapper> for &usize {
///     type Output = String;
///
///     fn visit_item(self, idx: usize) -> Self::Output {
///         assert_eq!(idx, 0);
///         format!("{}", self + 1)
///     }
/// }
///
/// impl Visit<MyMapper> for &String {
///     type Output = String;
///
///     fn visit_item(self, idx: usize) -> Self::Output {
///         let mut s = self.clone();
///         s.push_str(&format!("{idx}"));
///         s
///     }
/// }
///
/// let tupl = &(10usize, String::from("string-"), String::from("string-"));
/// assert_eq!(
///     MyMapper::into_iter(tupl.as_refs()).collect::<Vec<_>>(),
///     vec![String::from("11"), String::from("string-1"), String::from("string-2")]
/// );
/// ```
pub trait HListIntoIter<H: HList, U, const N: usize> {
    /// Returns an iterator over [Visit]ed elements
    fn into_iter(t: H) -> <[U; N] as IntoIterator>::IntoIter;
}

/// Statefull visitor where the state is a reference
pub trait VisitRef<S> {
    /// output of the visitor
    type Output;

    /// visitor function
    fn visit_item_ref(self, idx: usize, state: &S) -> Self::Output;
}

/// Statefull visitor where the state is a mutable reference
pub trait VisitMut<S> {
    /// output of the visitor
    type Output;

    /// visitor function
    fn visit_item_mut(self, idx: usize, state: &mut S) -> Self::Output;
}

/// Tuple visitor that takes a reference to a state
///
/// This trait is automatically implemented on HLists where all elements implement the [VisitRef] trait
///
/// Example with tuples:
/// ```
/// # use tuplify::VisitRef;
/// # use tuplify::VisitorRef;
/// struct MyVisitor(usize, String);
///
/// impl VisitRef<MyVisitor> for usize {
///     type Output = Self;
///
///     fn visit_item_ref(self, idx: usize, v: &MyVisitor) -> Self::Output {
///         assert_eq!(idx, 0);
///         self + v.0
///     }
/// }
///
/// impl VisitRef<MyVisitor> for &mut String {
///     type Output = Self;
///
///     fn visit_item_ref(self, idx: usize, v: &MyVisitor) -> Self::Output {
///         assert_eq!(idx, 1);
///         self.push_str(&v.1);
///         self
///     }
/// }
/// let visitor = MyVisitor(12, "hello".into());
/// let tupl = (10usize, &mut String::from("foo"));
/// assert_eq!(visitor.visit_ref(tupl), (22, &mut String::from("foohello")));
/// ```
///
/// Example with [struct@HCons]
/// ```
/// # use tuplify::VisitRef;
/// # use tuplify::VisitorRef;
/// # use tuplify::hcons;
/// struct MyVisitor(usize, String);
///
/// impl VisitRef<MyVisitor> for usize {
///     type Output = Self;
///
///     fn visit_item_ref(self, idx: usize, v: &MyVisitor) -> Self::Output {
///         assert_eq!(idx, 0);
///         self + v.0
///     }
/// }
///
/// impl VisitRef<MyVisitor> for String {
///     type Output = Self;
///
///     fn visit_item_ref(mut self, idx: usize, v: &MyVisitor) -> Self::Output {
///         assert_eq!(idx, 1);
///         self.push_str(&v.1);
///         self
///     }
/// }
///
/// let visitor = MyVisitor(12, "hello".into());
/// let tupl = hcons!(10usize, String::from("foo"));
/// assert_eq!(visitor.visit_ref(tupl), hcons!(22, String::from("foohello")));
/// ```
pub trait VisitorRef<T: HList> {
    /// Output of the visitor
    type Output: HList;

    /// Visit the given [HList] `T` with self as ref
    fn visit_ref(&self, t: T) -> Self::Output;
}

/// Tuple visitor that takes a mutable reference to a state
///
/// This trait is automatically implemented on HLists where all elements implement the [VisitMut] trait
///
/// Example with tuples:
/// ```
/// # use tuplify::VisitMut;
/// # use tuplify::VisitorMut;
/// struct MyVisitor(usize);
///
/// impl VisitMut<MyVisitor> for usize {
///     type Output = Self;
///
///     fn visit_item_mut(self, idx: usize, v: &mut MyVisitor) -> Self::Output {
///         assert_eq!(idx, 0);
///         v.0 += 1;
///         self
///     }
/// }
///
/// impl VisitMut<MyVisitor> for &mut String {
///     type Output = Self;
///
///     fn visit_item_mut(self, idx: usize, v: &mut MyVisitor) -> Self::Output {
///         assert_eq!(idx, 1);
///         v.0 += 1;
///         self
///     }
/// }
/// let mut visitor = MyVisitor(0);
/// let tupl = (10usize, &mut String::from("foo"));
/// assert_eq!(visitor.visit_mut(tupl), (10, &mut String::from("foo")));
/// assert_eq!(visitor.0, 2);
/// ```
///
/// Example with [struct@HCons]
/// ```
/// # use tuplify::VisitMut;
/// # use tuplify::VisitorMut;
/// # use tuplify::hcons;
/// # use tuplify::AsRefs;
/// struct MyVisitor(usize);
///
/// impl VisitMut<MyVisitor> for &usize {
///     type Output = Self;
///
///     fn visit_item_mut(self, idx: usize, v: &mut MyVisitor) -> Self::Output {
///         assert_eq!(idx, 0);
///         v.0 += 1;
///         self
///     }
/// }
///
/// impl VisitMut<MyVisitor> for &String {
///     type Output = Self;
///
///     fn visit_item_mut(self, idx: usize, v: &mut MyVisitor) -> Self::Output {
///         assert_eq!(idx, 1);
///         v.0 += 1;
///         self
///     }
/// }
/// let mut visitor = MyVisitor(0);
/// let tupl = hcons!(10usize, String::from("foo"));
/// assert_eq!(visitor.visit_mut(tupl.as_refs()), hcons!(&10, &String::from("foo")));
/// assert_eq!(visitor.0, 2);
/// ```
pub trait VisitorMut<T: HList> {
    /// Output of this visitor
    type Output: HList;

    /// Visits the given [HList]
    fn visit_mut(&mut self, t: T) -> Self::Output;
}

/// Folds a single [HList] element
pub trait FoldItem<T, A> {
    /// folds the given element
    fn fold_item(self, idx: usize, accum: A) -> A;
}

/// Folds the given [HList] `T` with the accumulator `A`
///
/// Example:
/// ```
/// # use tuplify::FoldItem;
/// # use tuplify::HListFold;
/// struct SumFold;
///
/// impl FoldItem<SumFold, usize> for usize {
///     fn fold_item(self, _: usize, accum: usize) -> usize { self + accum }
/// }
///
/// impl FoldItem<SumFold, usize> for String {
///     fn fold_item(self, _: usize, accum: usize) -> usize { self.len() + accum }
/// }
///
/// assert_eq!(SumFold::fold(0usize, (12usize, "foo".to_string())), 15);
/// ```
pub trait HListFold<T: HList, A> {
    /// folds the given tuple `T` with the accumulator `A`
    fn fold(accum: A, t: T) -> A;
}

/// Reverse implementation of [HListFold]
///
/// Folds the given [HList] `T` with the accumulator `A`
///
/// Example with tuples:
/// ```
/// # use tuplify::FoldItem;
/// # use tuplify::HListFold;
/// # use tuplify::FoldWith;
/// struct SumFold;
///
/// impl FoldItem<SumFold, usize> for usize {
///     fn fold_item(self, _: usize, accum: usize) -> usize { self + accum }
/// }
///
/// impl FoldItem<SumFold, usize> for String {
///     fn fold_item(self, _: usize, accum: usize) -> usize { self.len() + accum }
/// }
///
/// assert_eq!((12usize, "foo".to_string()).fold_with::<SumFold, _>(0), 15);
/// ```
///
/// Example with [struct@HCons]:
/// ```
/// # use tuplify::FoldItem;
/// # use tuplify::HListFold;
/// # use tuplify::FoldWith;
/// # use tuplify::hcons;
/// struct SumFold;
///
/// impl FoldItem<SumFold, usize> for usize {
///     fn fold_item(self, _: usize, accum: usize) -> usize { self + accum }
/// }
///
/// impl FoldItem<SumFold, usize> for String {
///     fn fold_item(self, _: usize, accum: usize) -> usize { self.len() + accum }
/// }
///
/// assert_eq!(hcons!(12usize, "foo".to_string()).fold_with::<SumFold, _>(0), 15);
/// ```
pub trait FoldWith: HList + Sized {
    /// Folds self with the `T` and `A`
    fn fold_with<T, A>(self, init: A) -> A
    where
        T: HListFold<Self, A>;
}

impl<L: HList + Sized> FoldWith for L {
    fn fold_with<T, A>(self, init: A) -> A
    where
        T: HListFold<Self, A>,
    {
        T::fold(init, self)
    }
}

// Everything else is generated for tuples up to a certain fixed length
macro_rules! gen_visitor_impls {
    () => {};
    ($head:ident $($tail:ident)*) => {
        gen_visitor_impls!($($tail) *);
        impl<M, $head, $($tail), *> Visitor<($head, $($tail), *)> for M
        where
            ($head, $($tail), *): HList,
            $head: Visit<M>,
            $($tail: Visit<M>), *
        {
            type Output = (<$head as Visit<M>>::Output, $(<$tail as Visit<M>>::Output), *);

            #[allow(non_snake_case)]
            fn visit(($head, $($tail), *): ($head, $($tail), *)) -> Self::Output {
                use paste::paste;
                paste!{ let [[<$head _t>], $([<$tail _t >]), *] = std::array::from_fn::<usize, { count_tokens!($head $($tail) *) }, _>(|x| x); };
                ($head.visit_item(paste!{[<$head _t>]}), $($tail.visit_item(paste!{[<$tail _t>]})), *)
            }
        }

        impl<M, $head, $($tail), *> Visitor<HCons!($head, $($tail), *)> for M
        where
            HCons!($head, $($tail), *): HList,
            $head: Visit<M>,
            $($tail: Visit<M>), *
        {
            type Output = HCons!(<$head as Visit<M>>::Output, $(<$tail as Visit<M>>::Output), *);

            #[allow(non_snake_case)]
            fn visit(hcons_pat!($head, $($tail), *): HCons!($head, $($tail), *)) -> Self::Output {
                use paste::paste;
                paste!{ let [[<$head _t>], $([<$tail _t >]), *] = std::array::from_fn::<usize, { count_tokens!($head $($tail) *) }, _>(|x| x); };
                hcons!($head.visit_item(paste!{[<$head _t>]}), $($tail.visit_item(paste!{[<$tail _t>]})), *)
            }
        }

        impl<M, U, $head, $($tail), *> HListIntoIter<($head, $($tail,) *), U, { count_tokens!($head $($tail) *) }> for M
        where
            ($head, $($tail,) *): HList,
            $head: Visit<M, Output = U>,
            $($tail: Visit<M, Output = U>), *
        {
            #[allow(non_snake_case)]
            fn into_iter(($head, $($tail), *): ($head, $($tail), *)) -> <[U; { count_tokens!($head $($tail) *) }] as IntoIterator>::IntoIter {
                use paste::paste;
                paste!{ let [[<$head _t>], $([<$tail _t >]), *] = std::array::from_fn::<usize, { count_tokens!($head $($tail) *) }, _>(|x| x); };
                [$head.visit_item(paste!{[<$head _t>]}), $($tail.visit_item(paste!{[<$tail _t>]})), *].into_iter()
            }
        }

        impl<M, U, $head, $($tail), *> HListIntoIter<HCons!($head, $($tail,) *), U, { count_tokens!($head $($tail) *) }> for M
        where
            ($head, $($tail,) *): HList,
            $head: Visit<M, Output = U>,
            $($tail: Visit<M, Output = U>), *
        {
            #[allow(non_snake_case)]
            fn into_iter(hcons_pat!($head, $($tail), *): HCons!($head, $($tail), *)) -> <[U; { count_tokens!($head $($tail) *) }] as IntoIterator>::IntoIter {
                use paste::paste;
                paste!{ let [[<$head _t>], $([<$tail _t >]), *] = std::array::from_fn::<usize, { count_tokens!($head $($tail) *) }, _>(|x| x); };
                [$head.visit_item(paste!{[<$head _t>]}), $($tail.visit_item(paste!{[<$tail _t>]})), *].into_iter()
            }
        }

        impl<M, $head, $($tail), *> VisitorRef<($head, $($tail), *)> for M
        where
            ($head, $($tail), *): HList,
            $head: VisitRef<Self>,
            $($tail: VisitRef<Self>), *
        {
            type Output = ($head::Output, $($tail::Output), *);

            #[allow(non_snake_case)]
            fn visit_ref(&self, ($head, $($tail), *): ($head, $($tail), *)) -> Self::Output {
                use paste::paste;
                paste!{ let [[<$head _t>], $([<$tail _t >]), *] = std::array::from_fn::<usize, { count_tokens!($head $($tail) *) }, _>(|x| x); };
                ($head.visit_item_ref(paste!{[<$head _t>]}, self), $($tail.visit_item_ref(paste!{[<$tail _t>]}, self)), *)
            }
        }

        impl<M, $head, $($tail), *> VisitorRef<HCons!($head, $($tail), *)> for M
        where
            HCons!($head, $($tail), *): HList,
            $head: VisitRef<Self>,
            $($tail: VisitRef<Self>), *
        {
            type Output = HCons!($head::Output, $($tail::Output), *);

            #[allow(non_snake_case)]
            fn visit_ref(&self, hcons_pat!($head, $($tail), *): HCons!($head, $($tail), *)) -> Self::Output {
                use paste::paste;
                paste!{ let [[<$head _t>], $([<$tail _t >]), *] = std::array::from_fn::<usize, { count_tokens!($head $($tail) *) }, _>(|x| x); };
                hcons!($head.visit_item_ref(paste!{[<$head _t>]}, self), $($tail.visit_item_ref(paste!{[<$tail _t>]}, self)), *)
            }
        }

        impl<M, $head, $($tail), *> VisitorMut<($head, $($tail), *)> for M
        where
            ($head, $($tail), *): HList,
            $head: VisitMut<Self>,
            $($tail: VisitMut<Self>), *
        {
            type Output = ($head::Output, $($tail::Output), *);

            #[allow(non_snake_case)]
            fn visit_mut(&mut self, ($head, $($tail), *): ($head, $($tail), *)) -> Self::Output {
                use paste::paste;
                paste!{ let [[<$head _t>], $([<$tail _t >]), *] = std::array::from_fn::<usize, { count_tokens!($head $($tail) *) }, _>(|x| x); };
                ($head.visit_item_mut(paste!{[<$head _t>]}, self), $($tail.visit_item_mut(paste!{[<$tail _t>]}, self)), *)
            }
        }

        impl<M, $head, $($tail), *> VisitorMut<HCons!($head, $($tail), *)> for M
        where
            HCons!($head, $($tail), *): HList,
            $head: VisitMut<Self>,
            $($tail: VisitMut<Self>), *
        {
            type Output = HCons!($head::Output, $($tail::Output), *);

            #[allow(non_snake_case)]
            fn visit_mut(&mut self, hcons_pat!($head, $($tail), *): HCons!($head, $($tail), *)) -> Self::Output {
                use paste::paste;
                paste!{ let [[<$head _t>], $([<$tail _t >]), *] = std::array::from_fn::<usize, { count_tokens!($head $($tail) *) }, _>(|x| x); };
                hcons!($head.visit_item_mut(paste!{[<$head _t>]}, self), $($tail.visit_item_mut(paste!{[<$tail _t>]}, self)), *)
            }
        }

        impl<M, A, $head, $($tail), *> HListFold<($head, $($tail), *), A> for M
        where
            ($head, $($tail), *): HList,
            $head: FoldItem<Self, A>,
            $($tail: FoldItem<Self, A>), *
        {
            #[allow(non_snake_case)]
            fn fold(accum: A, ($head, $($tail), *): ($head, $($tail), *)) -> A {
                use paste::paste;
                paste!{ let [[<$head _t>], $([<$tail _t >]), *] = std::array::from_fn::<usize, { count_tokens!($head $($tail) *) }, _>(|x| x); };
                let accum = $head.fold_item(paste!{[<$head _t>]}, accum);
                $(let accum = $tail.fold_item(paste!{[<$tail _t>]}, accum);) *
                accum
            }
        }

        impl<M, A, $head, $($tail), *> HListFold<HCons!($head, $($tail), *), A> for M
        where
            HCons!($head, $($tail), *): HList,
            $head: FoldItem<Self, A>,
            $($tail: FoldItem<Self, A>), *
        {
            #[allow(non_snake_case)]
            fn fold(accum: A, hcons_pat!($head, $($tail), *): HCons!($head, $($tail), *)) -> A {
                use paste::paste;
                paste!{ let [[<$head _t>], $([<$tail _t >]), *] = std::array::from_fn::<usize, { count_tokens!($head $($tail) *) }, _>(|x| x); };
                let accum = $head.fold_item(paste!{[<$head _t>]}, accum);
                $(let accum = $tail.fold_item(paste!{[<$tail _t>]}, accum);) *
                accum
            }
        }
    };
}

gen_visitor_impls!(T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32);

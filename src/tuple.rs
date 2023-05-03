//! [`Tuple`] specific implementations & traits

use crate::{hlist::*, Tuple};

/// Utility trait used to convert something into a [`crate::Tuple`].
///
/// Can be implemented for converting something into a tuple
pub trait IntoTuple {
    /// The type of the resulting tuple.
    type Output: Tuple;

    /// Converts the heterogeneous list into a tuple.
    ///
    /// Equivalent to `self.extend(())`.
    ///
    /// # Examples
    ///
    /// ```
    /// use tuplify::*;
    /// let ls = hcons![0, '1', "2"].into_tuple();
    ///
    /// assert_eq!(ls, (0, '1', "2"));
    /// ```
    ///
    /// ```
    /// use tuplify::*;
    /// let ls = hcons![].into_tuple();
    ///
    /// assert_eq!(ls, ());
    /// ```
    ///  
    /// ```
    /// use tuplify::*;
    /// let ls = hcons![42].into_tuple();
    ///
    /// assert_eq!(ls, (42,));
    /// ```
    fn into_tuple(self) -> Self::Output;
}

impl crate::seal::Tuple for () {}

impl HList for () {
    const LEN: usize = 0;
}

impl IntoTuple for () {
    type Output = Self;

    fn into_tuple(self) {}
}

impl<E> PushFront<E> for () {
    type Output = (E,);

    fn push_front(self, element: E) -> Self::Output { (element,) }
}

impl<E> PushBack<E> for () {
    type Output = (E,);

    fn push_back(self, element: E) -> Self::Output { (element,) }
}

impl Unpack for () {
    type Output = Self;

    fn unpack(self) -> Self::Output { self }
}

// Also implement the special case of `UnpackOne` for `(T,)`
impl<T> Unpack for (T,) {
    type Output = T;

    fn unpack(self) -> Self::Output { self.0 }
}

impl<T: HList> Extend<T> for () {
    type Output = T;

    fn extend(self, other: T) -> Self::Output { other }
}

impl AsRefs<'_> for () {
    type Output = ();

    fn as_refs(&self) {}
}

impl AsMuts<'_> for () {
    type Output = ();

    fn as_muts(&mut self) {}
}

impl IntoOpts for () {
    type Output = ();

    fn into_opts(self) {}
}

impl Reverse for () {
    type Output = ();

    fn rev(self) {}
}

impl<O, F: FnOnce() -> O> FunOnce<()> for F {
    type Output = O;

    fn call_fun_once(self, _: ()) -> O { self() }
}

impl<O, F: FnMut() -> O> FunMut<()> for F {
    fn call_fun_mut(&mut self, _: ()) -> O { self() }
}

impl<O, F: Fn() -> O> Fun<()> for F {
    fn call_fun(&self, _: ()) -> O { self() }
}

impl ValidateOpt for () {
    type Output = ();

    fn validate(self) -> Option<Self::Output> { Some(()) }
}

impl TryValidateOpt for () {
    type Output = ();

    fn try_validate(self) -> Result<Self::Output, Self> { Ok(()) }
}

impl<E> ValidateRes<E> for () {
    type Output = ();

    fn validate(self) -> Result<Self::Output, E> { Ok(()) }
}

impl TryValidateRes for () {
    type Output = ();

    fn try_validate(self) -> Result<Self::Output, Self> { Ok(()) }
}

impl TryPopBack for () {
    type Back = Never;
    type Front = NeverList;

    fn try_pop_back(self) -> Option<(Self::Back, Self::Front)> { None }
}

// Everything else is generated for tuples up to a certain fixed length
macro_rules! gen_tuple_hlist {
    () => {};
    ($head:ident $($tail:ident)*) => {
        gen_tuple_hlist!($($tail)*);

        impl<$head, $($tail,) *> crate::seal::Tuple for ($head, $($tail,) *) {}

        impl<$head, $($tail,) *> IntoTuple for ($head, $($tail,) *) {
            type Output = Self;

            fn into_tuple(self) -> Self::Output { self }
        }

        impl<$head, $($tail,) *> HList for ($head, $($tail,) *) {
            const LEN: usize = 1 + <($($tail,) *) as HList>::LEN;
        }

        impl<$head, $($tail,) *> Uncons for ($head, $($tail,) *) {
            type Head = $head;
            type Tail = ($($tail,) *);

            #[allow(non_snake_case)]
            fn uncons(self) -> (Self::Head, Self::Tail) {
                let (h, $($tail,) *) = self;
                (h, ($($tail,) *))
            }
        }

        impl<H, $head, $($tail,) *> PushFront<H> for ($head, $($tail,) *)
            where (H, $head, $($tail,) *): HList
        {
            type Output = (H, $head, $($tail,) *);

            #[allow(non_snake_case)]
            fn push_front(self, head: H) -> Self::Output {
                let (h, $($tail,) *) = self;
                (head, h, $($tail,) *)
            }
        }

        impl<H, $head, $($tail,) *> Unpack for (H, $head, $($tail,) *) where Self: HList {
            type Output = Self;

            fn unpack(self) -> Self::Output { self }
        }

        impl<'a, $head: 'a, $($tail: 'a,) *> AsRefs<'a> for ($head, $($tail,) *) {
            type Output = (&'a $head, $(&'a $tail,) *);

            #[allow(non_snake_case)]
            fn as_refs(&'a self) -> Self::Output {
                let ($head, $($tail,) *) = self;
                ($head, $($tail,) *)
            }
        }

        impl<'a, $head: 'a, $($tail: 'a,) *> AsMuts<'a> for ($head, $($tail,) *) {
            type Output = (&'a mut $head, $(&'a mut $tail,) *);

            #[allow(non_snake_case)]
            fn as_muts(&'a mut self) -> Self::Output {
                let ($head, $($tail,) *) = self;
                ($head, $($tail,) *)
            }
        }

        impl<O, F, $head, $($tail,) *> FunOnce<($head, $($tail,) *)> for F
        where
            F: FnOnce($head, $($tail,) *) -> O,
        {
            type Output = F::Output;

            #[allow(non_snake_case)]
            fn call_fun_once(self, ($head, $($tail,) *): ($head, $($tail,) *)) -> O {
                self($head, $($tail,) *)
            }
        }

        impl<O, F, $head, $($tail,) *> FunMut<($head, $($tail,) *)> for F
        where
            F: FnMut($head, $($tail,) *) -> O,
        {
            #[allow(non_snake_case)]
            fn call_fun_mut(&mut self, ($head, $($tail,) *): ($head, $($tail,) *)) -> O {
                self($head, $($tail,) *)
            }
        }

        impl<O, F, $head, $($tail,) *> Fun<($head, $($tail,) *)> for F
        where
            F: Fn($head, $($tail,) *) -> O,
        {
            #[allow(non_snake_case)]
            fn call_fun(&self, ($head, $($tail,) *): ($head, $($tail,) *)) -> O {
                self($head, $($tail,) *)
            }
        }
    };
}

gen_tuple_hlist!(T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{hcons::IntoHCons, hlist};

    #[test]
    fn test_tuple() {
        let frob = (1, 2).extend((2, 2, 5, 6)).extend(("hello", "world"));
        let x = (1, 2, 2, 2, 5, 6, "hello", "world");
        assert_eq!(frob, x);
        assert_eq!(frob.len(), x.len());
        assert_eq!(frob.len(), 8);
        assert_eq!(frob.rev(), ("world", "hello", 6, 5, 2, 2, 2, 1));
        assert_eq!(("foo", "bar", "boo", "zoo").rev(), ("zoo", "boo", "bar", "foo"));
        #[allow(clippy::unit_cmp)]
        {
            assert_eq!(().unpack(), ());
        }
        assert_eq!((1,).unpack(), 1);
        assert_eq!((1, 2).unpack(), (1, 2));
        assert_eq!((1, 2, 3).uncons(), (1, (2, 3)));
        assert_eq!((1, 2, 3).into_opts(), (Some(1), Some(2), Some(3)));

        assert_eq!(
            (Some(1), Some(2)).into_hcons().validate().map(|l| l.into_tuple()),
            Some((1, 2))
        );
        assert_eq!(
            (Result::<u32, ()>::Ok(1), Ok(1))
                .into_hcons()
                .validate()
                .map(|l| l.into_tuple()),
            Ok((1, 1))
        );
        assert_eq!(
            (Result::<u32, ()>::Err(()), Ok(1))
                .into_hcons()
                .validate()
                .map(|l| l.into_tuple()),
            Err(())
        );

        assert_eq!((Some(1), Option::<u32>::None).try_validate(), Err((Some(1), None)));
        assert_eq!((Some(1), Some(2)).validate(), Some((1, 2)));
        assert_eq!((Result::<u32, ()>::Ok(1), Ok(1)).validate(), Ok((1, 1)));
        assert_eq!(
            (Result::<u32, ()>::Ok(1), Result::<u32, i8>::Ok(1)).try_validate(),
            Ok((1, 1))
        );
        assert_eq!((Result::<u32, ()>::Err(()), Ok(1)).validate(), Err(()));
        assert_eq!(
            (Result::<u32, ()>::Err(()), Result::<u32, u8>::Ok(1)).try_validate(),
            Err((Err(()), Ok(1)))
        );

        assert_eq!((1, 2, 3).as_refs(), (&1, &2, &3));
        assert_eq!(().into_tuple(), ());
        assert_eq!(hlist::TryValidateOpt::try_validate(()), Ok(()));
        assert_eq!(hlist::TryValidateRes::try_validate(()), Ok(()));
    }
}

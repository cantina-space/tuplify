//! [`HCons`] implementations & traits

use crate::{hlist::*, tuple::IntoTuple};

/// Heterogeneous List.
///
/// Heterogeneous lists are implemented as a static cons-list of tuples with [`HEmpty`], denoting the empty list.
///
/// `HCons<A, HEmpty>` is a list of one element, `HCons<A, HCons<B, HEmpty>>` is a list of two elements, and so on.
///
/// this type is used to generically implement things for [`HList`]s
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HCons<H, T>(pub H, pub T);

/// Constructs an [`HCons`] type.
///
/// # Examples
///
/// ```
/// # use tuplify::{HCons, hcons};
/// let empty: HCons![] = hcons![];
/// let hcons: HCons![Option<()>, bool, u8] = hcons![None, false, 0];
/// ```
#[macro_export]
macro_rules! HCons {
    () => { $crate::hcons::HEmpty };
    ($head:ty $(,) *) => { $crate::hcons::HCons<$head, $crate::hcons::HEmpty> };
    ($head:ty, $($tail:ty), * $(,) *) => { $crate::hcons::HCons<$head, $crate::HCons!($($tail), *)> };
}

/// Constructs an [`HCons`] value.
///
/// # Examples
///
/// ```
/// # use tuplify::{hcons, hcons::*};
/// assert_eq!(hcons![], HEmpty);
/// assert_eq!(hcons![Some(4), false, 0], HCons(Some(4), HCons(false, HCons(0, HEmpty))));
/// ```
#[macro_export]
macro_rules! hcons {
    () => { $crate::hcons::HEmpty };
    ($head:expr $(,) *) => { $crate::hcons::HCons($head, $crate::hcons::HEmpty) };
    ($head:expr, $($tail:expr), * $(,) *) => { $crate::hcons::HCons($head,  $crate::hcons!($($tail), *)) };
}

/// Constructs a pattern matching [`HCons`] values.
///
/// # Examples
///
/// ```
/// # use tuplify::{hcons, hcons_pat};
/// let hcons_pat![(a, b), (c, d)] = hcons![(1, 2), (3, 4)];
/// assert_eq!((a, b, c, d), (1, 2, 3, 4));
/// ```
#[macro_export]
macro_rules! hcons_pat {
    ($head:pat $(,) *) => { $crate::hcons::HCons($head, $crate::hcons::HEmpty) };
    ($head:pat, $($tail:pat), * $(,) *) => { $crate::hcons::HCons($head, $crate::hcons_pat!($($tail),*)) };
}

/// Trait for converting a heterogeneous list into a [`HCons`] list.
pub trait IntoHCons {
    /// The type of the resulting [`HCons`] list.
    type Output: HList;

    /// Converts the heterogeneous list into a [`HCons`] list.
    ///
    /// Equivalent to `self.extend(HEmpty)`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tuplify::{*, hlist::*, hcons::*, tuple::*};
    /// let ls = (0, '1', "2").into_hcons();
    ///
    /// assert_eq!(ls, hcons![0, '1', "2"]);
    /// ```
    ///
    /// ```
    /// # use tuplify::{*, hlist::*, hcons::*, tuple::*};
    /// let ls = ().into_hcons();
    ///
    /// assert_eq!(ls, hcons![]);
    /// ```
    ///
    /// ```
    /// # use tuplify::{*, hlist::*, hcons::*, tuple::*};
    /// let ls = (12,).into_hcons();
    ///
    /// assert_eq!(ls, hcons![12]);
    /// ```
    fn into_hcons(self) -> Self::Output;
}

impl<T: Extend<HEmpty>> IntoHCons for T
where
    <T as Extend<HEmpty>>::Output: HList,
{
    type Output = <T as Extend<HEmpty>>::Output;

    fn into_hcons(self) -> Self::Output { self.extend(HEmpty) }
}

/// The empty HCons.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HEmpty;

// Most base cases for recursive algorithms are implemented on `HEmpty`
impl IntoTuple for HEmpty {
    type Output = ();

    fn into_tuple(self) -> Self::Output {}
}

impl HList for HEmpty {
    const LEN: usize = 0;
}

impl<E> PushFront<E> for HEmpty {
    type Output = HCons<E, HEmpty>;

    fn push_front(self, element: E) -> Self::Output { HCons(element, HEmpty) }
}

impl<E> PushBack<E> for HEmpty {
    type Output = HCons<E, HEmpty>;

    fn push_back(self, element: E) -> Self::Output { HCons(element, HEmpty) }
}

impl Unpack for HEmpty {
    type Output = Self;

    fn unpack(self) -> Self::Output { self }
}

impl<T: HList> Extend<T> for HEmpty {
    type Output = T;

    fn extend(self, other: T) -> Self::Output { other }
}

impl AsRefs<'_> for HEmpty {
    type Output = HEmpty;

    fn as_refs(&self) -> Self::Output { HEmpty }
}

impl AsMuts<'_> for HEmpty {
    type Output = HEmpty;

    fn as_muts(&mut self) -> Self::Output { HEmpty }
}

impl IntoOpts for HEmpty {
    type Output = HEmpty;

    fn into_opts(self) -> Self::Output { HEmpty }
}

impl Reverse for HEmpty {
    type Output = HEmpty;

    fn rev(self) -> Self::Output { HEmpty }
}

impl<'a, H: 'a, T: AsRefs<'a>> AsRefs<'a> for HCons<H, T> {
    type Output = HCons<&'a H, <T as AsRefs<'a>>::Output>;

    fn as_refs(&'a self) -> Self::Output { HCons(&self.0, self.1.as_refs()) }
}

impl<'a, H: 'a, T: AsMuts<'a>> AsMuts<'a> for HCons<H, T> {
    type Output = HCons<&'a mut H, <T as AsMuts<'a>>::Output>;

    fn as_muts(&'a mut self) -> Self::Output { HCons(&mut self.0, self.1.as_muts()) }
}

impl<O, F: FnOnce() -> O> FunOnce<HEmpty> for F {
    type Output = O;

    fn call_fun_once(self, _: HEmpty) -> O { self() }
}

impl<O, F: FnMut() -> O> FunMut<HEmpty> for F {
    fn call_fun_mut(&mut self, _: HEmpty) -> O { self() }
}

impl<O, F: Fn() -> O> Fun<HEmpty> for F {
    fn call_fun(&self, _: HEmpty) -> O { self() }
}

impl ValidateOpt for HEmpty {
    type Output = HEmpty;

    fn validate(self) -> Option<Self::Output> { Some(HEmpty) }
}

impl TryValidateOpt for HEmpty {
    type Output = HEmpty;

    fn try_validate(self) -> Result<Self::Output, Self> { Ok(HEmpty) }
}

impl<E> ValidateRes<E> for HEmpty {
    type Output = HEmpty;

    fn validate(self) -> Result<Self::Output, E> { Ok(HEmpty) }
}

impl TryValidateRes for HEmpty {
    type Output = HEmpty;

    fn try_validate(self) -> Result<Self::Output, Self> { Ok(HEmpty) }
}

impl<H, T, F> Fun<HCons<H, T>> for F
where
    T: HList,
    HCons<H, T>: IntoTuple,
    <HCons<H, T> as IntoTuple>::Output: HList,
    F: Fun<<HCons<H, T> as IntoTuple>::Output>,
{
    fn call_fun(&self, l: HCons<H, T>) -> Self::Output { self.call_fun(l.into_tuple()) }
}

impl<H, T, F> FunMut<HCons<H, T>> for F
where
    T: HList,
    HCons<H, T>: IntoTuple,
    <HCons<H, T> as IntoTuple>::Output: HList,
    F: FunMut<<HCons<H, T> as IntoTuple>::Output>,
{
    fn call_fun_mut(&mut self, l: HCons<H, T>) -> Self::Output {
        self.call_fun_mut(l.into_tuple())
    }
}

impl<H, T, F> FunOnce<HCons<H, T>> for F
where
    T: HList,
    HCons<H, T>: IntoTuple,
    <HCons<H, T> as IntoTuple>::Output: HList,
    F: FunOnce<<HCons<H, T> as IntoTuple>::Output>,
{
    type Output = <F as FunOnce<<HCons<H, T> as IntoTuple>::Output>>::Output;

    fn call_fun_once(self, l: HCons<H, T>) -> Self::Output {
        self.call_fun_once(l.into_tuple())
    }
}

impl<H, T: IntoTuple> IntoTuple for HCons<H, T>
where
    <T as IntoTuple>::Output: PushFront<H>,
    <<T as IntoTuple>::Output as PushFront<H>>::Output: crate::Tuple,
{
    type Output = <<T as IntoTuple>::Output as PushFront<H>>::Output;

    fn into_tuple(self) -> Self::Output {
        let HCons(x, y) = self;
        (x,).extend(y.into_tuple())
    }
}

impl<H, T: HList> Uncons for HCons<H, T> {
    type Head = H;
    type Tail = T;

    fn uncons(self) -> (Self::Head, Self::Tail) { (self.0, self.1) }
}

impl<H, T: HList> HList for HCons<H, T> {
    const LEN: usize = 1 + T::LEN;
}

impl<H, T: HList, E> PushFront<E> for HCons<H, T> {
    type Output = HCons<E, HCons<H, T>>;

    fn push_front(self, element: E) -> Self::Output { HCons(element, self) }
}

impl<H> Unpack for HCons<H, HEmpty> {
    type Output = H;

    fn unpack(self) -> Self::Output { self.0 }
}

impl<H1, H2, T> Unpack for HCons<H1, HCons<H2, T>>
where
    Self: HList,
{
    type Output = Self;

    fn unpack(self) -> Self::Output { self }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hlist;

    #[test]
    fn test_hcons() {
        assert_eq!(hcons![10, 11], (10, 11).into_hcons());
        assert_eq!(hcons![10, 11].into_tuple(), (10, 11));
        let frob =
            hcons![1, 2].extend(hcons![2, 2, 5, 6]).extend(hcons!["hello", "world"]);
        let x = hcons![1, 2, 2, 2, 5, 6, "hello", "world"];
        assert_eq!(x.into_tuple(), (1, 2, 2, 2, 5, 6, "hello", "world"));
        assert_eq!(frob, x);
        assert_eq!(frob.len(), x.len());
        assert_eq!(frob.len(), 8);
        assert_eq!(frob.rev(), hcons!["world", "hello", 6, 5, 2, 2, 2, 1]);
        assert_eq!(
            hcons!["foo", "bar", "boo", "zoo"].rev(),
            hcons!["zoo", "boo", "bar", "foo"]
        );
        assert_eq!(hcons![1].unpack(), 1);
        assert_eq!(hcons![1, 2].unpack(), hcons![1, 2]);
        assert_eq!(hcons![1, 2, 3].into_opts(), hcons![Some(1), Some(2), Some(3)]);
        assert_eq!(
            hcons![Some(1), Option::<u32>::None].try_validate(),
            Err(hcons![Some(1), None])
        );
        assert_eq!(hcons![Some(1), Some(2)].validate(), Some(hcons![1, 2]));
        assert_eq!(hcons![Result::<u32, ()>::Ok(1), Ok(1)].validate(), Ok(hcons![1, 1]));
        assert_eq!(
            hcons![Result::<u32, ()>::Ok(1), Result::<u32, i8>::Ok(1)].try_validate(),
            Ok(hcons![1, 1])
        );
        assert_eq!(hcons![Result::<u32, ()>::Err(()), Ok(1)].validate(), Err(()));
        assert_eq!(
            hcons![Result::<u32, ()>::Err(()), Result::<u32, u8>::Ok(1)].try_validate(),
            Err(hcons![Err(()), Ok(1)])
        );
        assert_eq!(hcons![1, 2, 3].extend(HEmpty), hcons![1, 2, 3]);
        assert_eq!(hcons![1, 2, 3].extend(()), (1, 2, 3));
        assert_eq!(hcons![1, 2, 3].as_refs(), hcons![&1, &2, &3]);
        assert_eq!(HEmpty.unpack(), HEmpty);
        assert_eq!(HEmpty.as_muts(), HEmpty);
        assert_eq!(hlist::TryValidateOpt::try_validate(HEmpty), Ok(HEmpty));
        assert_eq!(hlist::TryValidateRes::try_validate(HEmpty), Ok(HEmpty));
        let mut foo = 10;
        let mut funm = |i| {
            foo += i;
        };
        funm.call_fun_mut(hcons!(12,));
        assert_eq!(foo, 22);
        let foo = Some(12);
        let funo = move |x, y| foo.unwrap() + x + y;
        assert_eq!(funo.call_fun_once(hcons!(1, 2)), 15);
        assert_eq!(hcons!(1, 2, 3, 4), [1, 2, 3, 4].into());
        let h = [1, 2, 3, 4].into();
        assert_eq!(hcons!(1, 2, 3, 4), h);
        assert_eq!((1, 2, 3, 4), h.into_tuple());
        assert_eq!([1, 2, 3, 4], Into::<[i32; 4]>::into(hcons!(1, 2, 3, 4)));
        assert_eq!([1, 2, 3, 4], Into::<[i32; 4]>::into((1, 2, 3, 4).into_hcons()));
    }
}

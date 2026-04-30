use core::marker::PhantomData;

use reborrow_generic::Reborrow;

use crate::back::RbBack;
use crate::error::ErrorSink;
use crate::error::std::Unexpected;
use crate::input::{In, Input};
use crate::parser::{Parser, ParserMut, ParserOnce, SkipParser, SkipParserMut, SkipParserOnce};

pub trait ExpectedItem<It> {
    fn eq_item(&self, actual: &It) -> bool;
}

impl<It: PartialEq> ExpectedItem<It> for It {
    #[inline]
    fn eq_item(&self, actual: &It) -> bool {
        self == actual
    }
}

impl<'a, It: PartialEq> ExpectedItem<It> for &'a It {
    #[inline]
    fn eq_item(&self, actual: &It) -> bool {
        *self == actual
    }
}

pub trait ItemSeq<It>: Clone {
    type Item: ExpectedItem<It>;
    type Iter: Iterator<Item = Self::Item>;
    fn iter(&self) -> Self::Iter;
}

impl<'a, It: PartialEq + Clone> ItemSeq<It> for &'a [It] {
    type Item = &'a It;
    type Iter = core::slice::Iter<'a, It>;
    #[inline]
    fn iter(&self) -> Self::Iter {
        (*self).iter()
    }
}

impl<'a, It: PartialEq + Clone, const N: usize> ItemSeq<It> for &'a [It; N] {
    type Item = &'a It;
    type Iter = core::slice::Iter<'a, It>;
    #[inline]
    fn iter(&self) -> Self::Iter {
        self.as_slice().iter()
    }
}

impl<'a> ItemSeq<char> for &'a str {
    type Item = char;
    type Iter = core::str::Chars<'a>;
    #[inline]
    fn iter(&self) -> Self::Iter {
        self.chars()
    }
}

/// Match an exact item sequence.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "hello!".test(tag("hello"));
/// assert_eq!(out, Some(()));
///
/// let expected = ['a', 'b', 'c'];
/// let out = "abc".test(tag(&expected));
/// assert_eq!(out, Some(()));
///
/// let out = "axc".test(tag(&expected));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn tag<S, A>(expected: S) -> Tag<S, A> {
    Tag(expected, PhantomData)
}

#[derive(Clone, Copy, Debug, Hash)]
pub struct Tag<S, A>(pub(crate) S, PhantomData<fn() -> A>);

#[inline]
fn run_tag<I, N, L, E, S>(mut i: In<I, N, L, E>, expected: S) -> Option<()>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    S: ItemSeq<I::Item>,
    Unexpected<I::Item>: Into<E::Error>,
{
    for expected in expected.iter() {
        let p0 = i.input.pos();
        match i.input.next() {
            Some(actual) if expected.eq_item(&actual) => {}
            Some(actual) => {
                let p1 = i.input.pos();
                E::push(
                    E::shorten_mut(&mut i.errors),
                    p0..p1,
                    Unexpected::Item(actual).into(),
                );
                return None;
            }
            None => {
                let p1 = i.input.pos();
                E::push(
                    E::shorten_mut(&mut i.errors),
                    p0..p1,
                    Unexpected::EndOfInput.into(),
                );
                return None;
            }
        }
    }
    Some(())
}

impl<I, N, L, E, S> SkipParserOnce<I, N, L, E> for Tag<S, (I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    S: ItemSeq<I::Item>,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        run_tag(i, self.0)
    }
}

impl<I, N, L, E, S> SkipParserMut<I, N, L, E> for Tag<S, (I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    S: ItemSeq<I::Item>,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        run_tag(i, self.0.clone())
    }
}

impl<I, N, L, E, S> SkipParser<I, N, L, E> for Tag<S, (I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    S: ItemSeq<I::Item>,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        run_tag(i, self.0.clone())
    }
}

impl<I, N, L, E, S> ParserOnce<I, N, L, E> for Tag<S, (I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    S: ItemSeq<I::Item>,
    Unexpected<I::Item>: Into<E::Error>,
{
    type Out = ();
    #[inline]
    fn parse_once(self, i: In<I, N, L, E>) -> Option<()> {
        run_tag(i, self.0)
    }
}

impl<I, N, L, E, S> ParserMut<I, N, L, E> for Tag<S, (I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    S: ItemSeq<I::Item>,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        run_tag(i, self.0.clone())
    }
}

impl<I, N, L, E, S> Parser<I, N, L, E> for Tag<S, (I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    S: ItemSeq<I::Item>,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<()> {
        run_tag(i, self.0.clone())
    }
}

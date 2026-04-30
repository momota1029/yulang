use core::marker::PhantomData;

use reborrow_generic::Reborrow;

use crate::back::RbBack;
use crate::error::ErrorSink;
use crate::error::std::Unexpected;
use crate::input::{In, Input};
use crate::parser::{Parser, ParserMut, ParserOnce, SkipParser, SkipParserMut, SkipParserOnce};

/// Match an exact string.
///
/// - On success: consumes the whole tag and returns `()`.
/// - On failure: pushes an `Unexpected` error at the mismatch location.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "hello!".test(tag("hello"));
/// assert_eq!(out, Some(()));
///
/// let out = "hxllo".test(tag("hello"));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn tag<A>(tag: &'static str) -> Tag<A> {
    Tag(tag, PhantomData)
}

#[derive(Clone, Copy, Debug, Hash)]
pub struct Tag<A>(pub(crate) &'static str, PhantomData<fn() -> A>);

#[inline]
fn run_tag<I, N, L, E>(mut i: In<I, N, L, E>, expected: &'static str) -> Option<()>
where
    I: Input<Item = char>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<I::Item>: Into<E::Error>,
{
    for expected in expected.chars() {
        let p0 = i.input.pos();
        match i.input.next() {
            Some(actual) if actual == expected => {}
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

impl<I, N, L, E> SkipParserOnce<I, N, L, E> for Tag<(I, N, L, E)>
where
    I: Input<Item = char>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        run_tag(i, self.0)
    }
}

impl<I, N, L, E> SkipParserMut<I, N, L, E> for Tag<(I, N, L, E)>
where
    I: Input<Item = char>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        run_tag(i, self.0)
    }
}

impl<I, N, L, E> SkipParser<I, N, L, E> for Tag<(I, N, L, E)>
where
    I: Input<Item = char>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        run_tag(i, self.0)
    }
}

impl<I, N, L, E> ParserOnce<I, N, L, E> for Tag<(I, N, L, E)>
where
    I: Input<Item = char>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<I::Item>: Into<E::Error>,
{
    type Out = ();
    #[inline]
    fn parse_once(self, i: In<I, N, L, E>) -> Option<()> {
        run_tag(i, self.0)
    }
}

impl<I, N, L, E> ParserMut<I, N, L, E> for Tag<(I, N, L, E)>
where
    I: Input<Item = char>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        run_tag(i, self.0)
    }
}

impl<I, N, L, E> Parser<I, N, L, E> for Tag<(I, N, L, E)>
where
    I: Input<Item = char>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<()> {
        run_tag(i, self.0)
    }
}

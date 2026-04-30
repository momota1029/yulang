use core::{fmt, marker::PhantomData, ops::Range};

use reborrow_generic::Reborrow;

use crate::back::{Back as _, RbBack};
use crate::error::ErrorSink;
use crate::error::std::{Unexpected, UnexpectedEndOfInput, UnexpectedItem};
use crate::input::{In, Input};
use crate::parser::{Parser, ParserMut, ParserOnce, SkipParser, SkipParserMut, SkipParserOnce};

pub mod set;
use set::{Complement, ItemSet};

fn push_error<I, N, L, E, Err>(i: &mut In<I, N, L, E>, range: Range<I::Pos>, error: Err)
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Err: Into<E::Error>,
{
    E::push(E::shorten_mut(&mut i.errors), range, error.into());
}

/// End-of-input check.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "".test(eoi);
/// assert_eq!(out, Some(()));
///
/// let out = "a".test(eoi);
/// assert_eq!(out, None);
/// ```
#[inline]
pub fn eoi<I, N, L, E>(mut i: In<I, N, L, E>) -> Option<()>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    UnexpectedItem<I::Item>: Into<E::Error>,
{
    let p0 = i.input.pos();
    match i.input.next() {
        None => Some(()),
        Some(item) => {
            let p1 = i.input.pos();
            push_error(&mut i, p0..p1, UnexpectedItem(item));
            None
        }
    }
}

/// Consume one item.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ab".test(any);
/// assert_eq!(out, Some('a'));
///
/// let out = "".test(any);
/// assert_eq!(out, None);
/// ```
#[inline]
pub fn any<I, N, L, E>(mut i: In<I, N, L, E>) -> Option<I::Item>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let p0 = i.input.pos();
    match i.input.next() {
        Some(item) => Some(item),
        None => {
            let p1 = i.input.pos();
            push_error(&mut i, p0..p1, UnexpectedEndOfInput);
            None
        }
    }
}

#[inline]
pub(crate) fn run_satisfy<I, N, L, E>(
    mut i: In<I, N, L, E>,
    f: impl FnOnce(&I::Item) -> bool,
) -> Option<I::Item>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<I::Item>: Into<E::Error>,
{
    let p0 = i.input.pos();
    match i.input.next() {
        Some(item) if f(&item) => Some(item),
        Some(item) => {
            let p1 = i.input.pos();
            push_error(&mut i, p0..p1, Unexpected::Item(item));
            None
        }
        None => {
            let p1 = i.input.pos();
            push_error(&mut i, p0..p1, Unexpected::EndOfInput);
            None
        }
    }
}

#[inline]
pub(crate) fn run_satisfy_map<I, N, L, E, O>(
    mut i: In<I, N, L, E>,
    f: impl FnOnce(I::Item) -> Option<O>,
) -> Option<O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<I::Item>: Into<E::Error>,
    I::Item: Clone,
{
    let p0 = i.input.pos();
    let checkpoint = i.checkpoint();
    match i.input.next() {
        Some(item) => {
            let item_for_err = item.clone();
            match f(item) {
                Some(out) => Some(out),
                None => {
                    let p1 = i.input.pos();
                    i.rollback(checkpoint);
                    push_error(&mut i, p0..p1, Unexpected::Item(item_for_err));
                    None
                }
            }
        }
        None => {
            let p1 = i.input.pos();
            i.rollback(checkpoint);
            push_error(&mut i, p0..p1, Unexpected::EndOfInput);
            None
        }
    }
}

/// Consume one item if the predicate holds.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ab".test(satisfy(|c| c == 'a'));
/// assert_eq!(out, Some('a'));
///
/// let out = "bb".test(satisfy(|c| c == 'a'));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn satisfy<F, It, A>(f: F) -> Satisfy<F, A>
where
    F: Fn(It) -> bool,
{
    Satisfy(f, PhantomData)
}

#[inline(always)]
pub fn satisfy_mut<F, It, A>(f: F) -> Satisfy<F, A>
where
    F: FnMut(It) -> bool,
{
    Satisfy(f, PhantomData)
}

#[inline(always)]
pub fn satisfy_once<F, It, A>(f: F) -> Satisfy<F, A>
where
    F: FnOnce(It) -> bool,
{
    Satisfy(f, PhantomData)
}

/// Consume one item and map it with a fallible function.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ab".test(satisfy_map(|c| (c == 'a').then_some(1)));
/// assert_eq!(out, Some(1));
///
/// let out = "bb".test(satisfy_map(|c| (c == 'a').then_some(1)));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn satisfy_map<F, It, O, A>(f: F) -> SatisfyMap<F, A>
where
    F: Fn(It) -> Option<O>,
{
    SatisfyMap(f, PhantomData)
}

/// Like `satisfy_map`, but accepts `FnOnce`.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ab".test(satisfy_map_once(|c| (c == 'a').then_some(1)));
/// assert_eq!(out, Some(1));
///
/// let out = "bb".test(satisfy_map_once(|c| (c == 'a').then_some(1)));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn satisfy_map_once<F, It, O, A>(f: F) -> SatisfyMap<F, A>
where
    F: FnOnce(It) -> Option<O>,
{
    SatisfyMap(f, PhantomData)
}

/// Like `satisfy_map`, but accepts `FnMut`.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ab".test(satisfy_map_mut(|c| (c == 'a').then_some(1)));
/// assert_eq!(out, Some(1));
///
/// let out = "bb".test(satisfy_map_mut(|c| (c == 'a').then_some(1)));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn satisfy_map_mut<F, It, O, A>(f: F) -> SatisfyMap<F, A>
where
    F: FnMut(It) -> Option<O>,
{
    SatisfyMap(f, PhantomData)
}

pub struct Satisfy<F, A = ()>(F, PhantomData<fn() -> A>);
impl<F: Clone, A> Clone for Satisfy<F, A> {
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}
impl<F: Copy, A> Copy for Satisfy<F, A> {}
impl<F: fmt::Debug, A> fmt::Debug for Satisfy<F, A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<I, N, L, E, F, It> SkipParserOnce<I, N, L, E> for Satisfy<F, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    F: FnOnce(It) -> bool,
    It: Clone,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        run_satisfy(i, |item| (self.0)(item.clone())).map(|_| ())
    }
}

impl<I, N, L, E, F, It> SkipParserMut<I, N, L, E> for Satisfy<F, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    F: FnMut(It) -> bool,
    It: Clone,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        run_satisfy(i, |item| (self.0)(item.clone())).map(|_| ())
    }
}

impl<I, N, L, E, F, It> SkipParser<I, N, L, E> for Satisfy<F, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    F: Fn(It) -> bool,
    It: Clone,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        run_satisfy(i, |item| (self.0)(item.clone())).map(|_| ())
    }
}

impl<I, N, L, E, F, It> ParserOnce<I, N, L, E> for Satisfy<F, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    F: FnOnce(It) -> bool,
    It: Clone,
{
    type Out = It;
    #[inline]
    fn parse_once(self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_satisfy(i, |item| (self.0)(item.clone()))
    }
}

impl<I, N, L, E, F, It> ParserMut<I, N, L, E> for Satisfy<F, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    F: FnMut(It) -> bool,
    It: Clone,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_satisfy(i, |item| (self.0)(item.clone()))
    }
}

impl<I, N, L, E, F, It> Parser<I, N, L, E> for Satisfy<F, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    F: Fn(It) -> bool,
    It: Clone,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_satisfy(i, |item| (self.0)(item.clone()))
    }
}

pub struct SatisfyMap<F, A = ()>(F, PhantomData<fn() -> A>);
impl<F: Clone, A> Clone for SatisfyMap<F, A> {
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}
impl<F: Copy, A> Copy for SatisfyMap<F, A> {}
impl<F: fmt::Debug, A> fmt::Debug for SatisfyMap<F, A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<I, N, L, E, F, It, O> SkipParserOnce<I, N, L, E> for SatisfyMap<F, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    F: FnOnce(It) -> Option<O>,
    It: Clone,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        run_satisfy_map(i, self.0).map(|_| ())
    }
}

impl<I, N, L, E, F, It, O> SkipParserMut<I, N, L, E> for SatisfyMap<F, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    F: FnMut(It) -> Option<O>,
    It: Clone,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        run_satisfy_map(i, |item| (self.0)(item)).map(|_| ())
    }
}

impl<I, N, L, E, F, It, O> SkipParser<I, N, L, E> for SatisfyMap<F, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    F: Fn(It) -> Option<O>,
    It: Clone,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        run_satisfy_map(i, |item| (self.0)(item)).map(|_| ())
    }
}

impl<I, N, L, E, F, It, O> ParserOnce<I, N, L, E> for SatisfyMap<F, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    F: FnOnce(It) -> Option<O>,
    It: Clone,
{
    type Out = O;
    #[inline]
    fn parse_once(self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_satisfy_map(i, self.0)
    }
}

impl<I, N, L, E, F, It, O> ParserMut<I, N, L, E> for SatisfyMap<F, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    F: FnMut(It) -> Option<O>,
    It: Clone,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_satisfy_map(i, |item| (self.0)(item))
    }
}

impl<I, N, L, E, F, It, O> Parser<I, N, L, E> for SatisfyMap<F, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    F: Fn(It) -> Option<O>,
    It: Clone,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_satisfy_map(i, |item| (self.0)(item))
    }
}

/// Match a specific item.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ab".test(item('a'));
/// assert_eq!(out, Some('a'));
///
/// let out = "bb".test(item('a'));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn item<T, It, A>(item: T) -> Item<T, It, A> {
    Item(item, PhantomData)
}

/// Alias of `item` (kept for readability).
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ab".test(item_of('a'));
/// assert_eq!(out, Some('a'));
///
/// let out = "bb".test(item_of('a'));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn item_of<T, It, A>(item: T) -> Item<T, It, A> {
    Item(item, PhantomData)
}

pub struct Item<T, It = T, A = ()>(T, PhantomData<fn() -> (It, A)>);
impl<T: Clone, It, A> Clone for Item<T, It, A> {
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}
impl<T: Copy, It, A> Copy for Item<T, It, A> {}
impl<T: fmt::Debug, It, A> fmt::Debug for Item<T, It, A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<I, N, L, E, T, It> SkipParserOnce<I, N, L, E> for Item<T, It, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    T: PartialEq<It>,
    It: Clone,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        run_satisfy(i, |it| self.0 == it.clone()).map(|_| ())
    }
}

impl<I, N, L, E, T, It> SkipParserMut<I, N, L, E> for Item<T, It, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    T: PartialEq<It>,
    It: Clone,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        run_satisfy(i, |it| self.0 == it.clone()).map(|_| ())
    }
}

impl<I, N, L, E, T, It> SkipParser<I, N, L, E> for Item<T, It, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    T: PartialEq<It>,
    It: Clone,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        run_satisfy(i, |it| self.0 == it.clone()).map(|_| ())
    }
}

impl<I, N, L, E, T, It> ParserOnce<I, N, L, E> for Item<T, It, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    T: PartialEq<It>,
    It: Clone,
{
    type Out = It;
    #[inline]
    fn parse_once(self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_satisfy(i, |it| self.0 == it.clone())
    }
}

impl<I, N, L, E, T, It> ParserMut<I, N, L, E> for Item<T, It, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    T: PartialEq<It>,
    It: Clone,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_satisfy(i, |it| self.0 == it.clone())
    }
}

impl<I, N, L, E, T, It> Parser<I, N, L, E> for Item<T, It, (I, N, L, E)>
where
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
    T: PartialEq<It>,
    It: Clone,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_satisfy(i, |it| self.0 == it.clone())
    }
}

/// Match any item in the given set.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ab".test(one_of("ab"));
/// assert_eq!(out, Some('a'));
///
/// let out = "cd".test(one_of("ab"));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn one_of<S, It, A>(items: S) -> OneOf<S::Copyable, A>
where
    S: ItemSet<It>,
{
    OneOf(items.into_copyable(), PhantomData)
}

/// Match any item not in the given set.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ba".test(none_of("a"));
/// assert_eq!(out, Some('b'));
///
/// let out = "a".test(none_of("a"));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn none_of<S, It, A>(items: S) -> OneOf<Complement<S::Copyable>, A>
where
    S: ItemSet<It>,
{
    OneOf(items.into_copyable().complement(), PhantomData)
}

pub struct OneOf<S, A = ()>(S, PhantomData<fn() -> A>);
impl<S: Clone, A> Clone for OneOf<S, A> {
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}
impl<S: Copy, A> Copy for OneOf<S, A> {}
impl<S: fmt::Debug, A> fmt::Debug for OneOf<S, A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<S, I, N, L, E, It> SkipParserOnce<I, N, L, E> for OneOf<S, (I, N, L, E)>
where
    S: ItemSet<It>,
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        run_satisfy(i, |item| self.0.has(item)).map(|_| ())
    }
}

impl<S, I, N, L, E, It> SkipParserMut<I, N, L, E> for OneOf<S, (I, N, L, E)>
where
    S: ItemSet<It>,
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        run_satisfy(i, |item| self.0.has(item)).map(|_| ())
    }
}

impl<S, I, N, L, E, It> SkipParser<I, N, L, E> for OneOf<S, (I, N, L, E)>
where
    S: ItemSet<It>,
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        run_satisfy(i, |item| self.0.has(item)).map(|_| ())
    }
}

impl<S, I, N, L, E, It> ParserOnce<I, N, L, E> for OneOf<S, (I, N, L, E)>
where
    S: ItemSet<It>,
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
{
    type Out = It;
    #[inline]
    fn parse_once(self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_satisfy(i, |item| self.0.has(item))
    }
}

impl<S, I, N, L, E, It> ParserMut<I, N, L, E> for OneOf<S, (I, N, L, E)>
where
    S: ItemSet<It>,
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_satisfy(i, |item| self.0.has(item))
    }
}

impl<S, I, N, L, E, It> Parser<I, N, L, E> for OneOf<S, (I, N, L, E)>
where
    S: ItemSet<It>,
    I: Input<Item = It>,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Unexpected<It>: Into<E::Error>,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_satisfy(i, |item| self.0.has(item))
    }
}

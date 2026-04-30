use core::marker::PhantomData;
use std::borrow::Cow;
use std::ops::Range;

use reborrow_generic::{Reborrow, Reborrowed};

use crate::input::{In, IsCut, SeqInput, ToSpan};
use crate::parser::{Parser, ParserMut, ParserOnce, SkipParser, SkipParserMut, SkipParserOnce};
use crate::{Back as _, ErrorSink, Input, RbBack};

pub struct RefParser<'a, P>(pub(crate) &'a P);

impl<P, I, N, L, E> SkipParserOnce<I, N, L, E> for RefParser<'_, P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard(i)
    }
}

impl<P, I, N, L, E> SkipParserMut<I, N, L, E> for RefParser<'_, P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard(i)
    }
}

impl<P, I, N, L, E> SkipParser<I, N, L, E> for RefParser<'_, P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard(i)
    }
}

impl<P, I, N, L, E> ParserOnce<I, N, L, E> for RefParser<'_, P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
{
    type Out = P::Out;
    #[inline]
    fn parse_once(self, i: In<I, N, L, E>) -> Option<Self::Out> {
        self.0.parse(i)
    }
}

impl<P, I, N, L, E> ParserMut<I, N, L, E> for RefParser<'_, P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<Self::Out> {
        self.0.parse(i)
    }
}

impl<P, I, N, L, E> Parser<I, N, L, E> for RefParser<'_, P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<Self::Out> {
        self.0.parse(i)
    }
}

pub struct MutParser<'a, P>(pub(crate) &'a mut P);

impl<P, I, N, L, E> SkipParserOnce<I, N, L, E> for MutParser<'_, P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard_mut(i)
    }
}

impl<P, I, N, L, E> SkipParserMut<I, N, L, E> for MutParser<'_, P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard_mut(i)
    }
}

impl<P, I, N, L, E> SkipParser<I, N, L, E> for MutParser<'_, P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard(i)
    }
}

impl<P, I, N, L, E> ParserOnce<I, N, L, E> for MutParser<'_, P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
{
    type Out = P::Out;
    #[inline]
    fn parse_once(self, i: In<I, N, L, E>) -> Option<Self::Out> {
        self.0.parse_mut(i)
    }
}

impl<P, I, N, L, E> ParserMut<I, N, L, E> for MutParser<'_, P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<Self::Out> {
        self.0.parse_mut(i)
    }
}

impl<P, I, N, L, E> Parser<I, N, L, E> for MutParser<'_, P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<Self::Out> {
        self.0.parse(i)
    }
}

pub struct RefOrMutParser<'a, P, I, N, L, E>
where
    P: ParserMut<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    inner: RefOrMutParserInner<'a, P, I, N, L, E>,
}

impl<'a, P, I, N, L, E> RefOrMutParser<'a, P, I, N, L, E>
where
    P: ParserMut<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    pub fn new_mut(parser: &'a mut P) -> Self {
        Self {
            inner: RefOrMutParserInner::Mut(parser),
        }
    }
}

impl<'a, P, I, N, L, E> RefOrMutParser<'a, P, I, N, L, E>
where
    P: Parser<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    pub fn new_ref(parser: &'a P) -> Self {
        Self {
            inner: RefOrMutParserInner::Ref(parser, P::parse),
        }
    }
}

enum RefOrMutParserInner<'a, P, I, N, L, E>
where
    P: ParserMut<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    Ref(&'a P, fn(&P, In<I, N, L, E>) -> Option<P::Out>),
    Mut(&'a mut P),
}

impl<'a, P, I, N, L, E> SkipParserOnce<I, N, L, E> for RefOrMutParser<'a, P, I, N, L, E>
where
    P: ParserMut<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_once(i).map(|_| ())
    }
}

impl<'a, P, I, N, L, E> SkipParserMut<I, N, L, E> for RefOrMutParser<'a, P, I, N, L, E>
where
    P: ParserMut<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_mut(i).map(|_| ())
    }
}

impl<'a, P, I, N, L, E> ParserOnce<I, N, L, E> for RefOrMutParser<'a, P, I, N, L, E>
where
    P: ParserMut<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    type Out = P::Out;
    #[inline]
    fn parse_once(self, input: In<I, N, L, E>) -> Option<Self::Out> {
        match self.inner {
            RefOrMutParserInner::Ref(p, f) => f(p, input),
            RefOrMutParserInner::Mut(p) => p.parse_mut(input),
        }
    }
}

impl<'a, P, I, N, L, E> ParserMut<I, N, L, E> for RefOrMutParser<'a, P, I, N, L, E>
where
    P: ParserMut<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    #[inline]
    fn parse_mut(&mut self, input: In<I, N, L, E>) -> Option<Self::Out> {
        match &mut self.inner {
            RefOrMutParserInner::Ref(p, f) => f(p, input),
            RefOrMutParserInner::Mut(p) => p.parse_mut(input),
        }
    }
}

pub struct RefOrMutSkipParser<'a, P, I, N, L, E>
where
    P: SkipParserMut<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    inner: RefOrMutSkipParserInner<'a, P, I, N, L, E>,
}

impl<'a, P, I, N, L, E> RefOrMutSkipParser<'a, P, I, N, L, E>
where
    P: SkipParserMut<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    pub fn new_mut(parser: &'a mut P) -> Self {
        Self {
            inner: RefOrMutSkipParserInner::Mut(parser),
        }
    }
}

impl<'a, P, I, N, L, E> RefOrMutSkipParser<'a, P, I, N, L, E>
where
    P: SkipParser<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    pub fn new_ref(parser: &'a P) -> Self {
        Self {
            inner: RefOrMutSkipParserInner::Ref(parser, P::discard),
        }
    }
}

enum RefOrMutSkipParserInner<'a, P, I, N, L, E>
where
    P: SkipParserMut<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    Ref(&'a P, fn(&P, In<I, N, L, E>) -> Option<()>),
    Mut(&'a mut P),
}

impl<'a, P, I, N, L, E> SkipParserOnce<I, N, L, E> for RefOrMutSkipParser<'a, P, I, N, L, E>
where
    P: SkipParserMut<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    #[inline]
    fn discard_once(self, input: In<I, N, L, E>) -> Option<()> {
        match self.inner {
            RefOrMutSkipParserInner::Ref(p, f) => f(p, input),
            RefOrMutSkipParserInner::Mut(p) => p.discard_mut(input),
        }
    }
}

impl<'a, P, I, N, L, E> SkipParserMut<I, N, L, E> for RefOrMutSkipParser<'a, P, I, N, L, E>
where
    P: SkipParserMut<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    #[inline]
    fn discard_mut(&mut self, input: In<I, N, L, E>) -> Option<()> {
        match &mut self.inner {
            RefOrMutSkipParserInner::Ref(p, f) => f(p, input),
            RefOrMutSkipParserInner::Mut(p) => p.discard_mut(input),
        }
    }
}

pub fn from_fn_once<F, O, I, N, L, E>(f: F) -> F
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: FnOnce(In<I, N, L, E>) -> Option<O>,
{
    f
}

impl<F, I, N, L, E, O> SkipParserOnce<I, N, L, E> for F
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: FnOnce(In<I, N, L, E>) -> Option<O>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        (self)(i).map(|_| ())
    }
}

impl<F, I, N, L, E, O> ParserOnce<I, N, L, E> for F
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: FnOnce(In<I, N, L, E>) -> Option<O>,
{
    type Out = O;
    #[inline]
    fn parse_once(self, i: In<I, N, L, E>) -> Option<Self::Out> {
        (self)(i)
    }
}

pub fn from_fn_mut<F, O, I, N, L, E>(f: F) -> F
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: FnMut(In<I, N, L, E>) -> Option<O>,
{
    f
}

impl<F, I, N, L, E, O> SkipParserMut<I, N, L, E> for F
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: FnMut(In<I, N, L, E>) -> Option<O>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        (self)(i).map(|_| ())
    }
}

impl<F, I, N, L, E, O> ParserMut<I, N, L, E> for F
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: FnMut(In<I, N, L, E>) -> Option<O>,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<Self::Out> {
        (self)(i)
    }
}

pub fn from_fn<F, O, I, N, L, E>(f: F) -> F
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: Fn(In<I, N, L, E>) -> Option<O>,
{
    f
}

impl<F, I, N, L, E, O> SkipParser<I, N, L, E> for F
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: Fn(In<I, N, L, E>) -> Option<O>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        (self)(i).map(|_| ())
    }
}

impl<F, I, N, L, E, O> Parser<I, N, L, E> for F
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: Fn(In<I, N, L, E>) -> Option<O>,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<Self::Out> {
        (self)(i)
    }
}

pub struct Value<O, A>(O, PhantomData<fn() -> A>);

/// Always succeed with a constant value.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "".test(value(1));
/// assert_eq!(out, Some(1));
///
/// let out = "abc".test(value(2));
/// assert_eq!(out, Some(2));
/// ```
#[inline(always)]
pub fn value<I, N, L, E, O>(value: O) -> Value<O, (I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    Value(value, PhantomData)
}

impl<I, N, L, E, O> SkipParserOnce<I, N, L, E> for Value<O, (I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    #[inline]
    fn discard_once(self, _i: In<I, N, L, E>) -> Option<()> {
        Some(())
    }
}

impl<I, N, L, E, O> ParserOnce<I, N, L, E> for Value<O, (I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    type Out = O;
    #[inline]
    fn parse_once(self, _i: In<I, N, L, E>) -> Option<Self::Out> {
        Some(self.0)
    }
}

impl<I, N, L, E, O> SkipParserMut<I, N, L, E> for Value<O, (I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    #[inline]
    fn discard_mut(&mut self, _i: In<I, N, L, E>) -> Option<()> {
        Some(())
    }
}

impl<I, N, L, E, O> ParserMut<I, N, L, E> for Value<O, (I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    O: Clone,
{
    #[inline]
    fn parse_mut(&mut self, _i: In<I, N, L, E>) -> Option<Self::Out> {
        Some(self.0.clone())
    }
}

impl<I, N, L, E, O> SkipParser<I, N, L, E> for Value<O, (I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    #[inline]
    fn discard(&self, _i: In<I, N, L, E>) -> Option<()> {
        Some(())
    }
}

impl<I, N, L, E, O> Parser<I, N, L, E> for Value<O, (I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    O: Clone,
{
    #[inline]
    fn parse(&self, _i: In<I, N, L, E>) -> Option<Self::Out> {
        Some(self.0.clone())
    }
}

pub struct IsTrue<A>(bool, PhantomData<fn() -> A>);

/// Succeed if the given boolean is true.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "".test(is_true(true));
/// assert_eq!(out, Some(()));
///
/// let out = "".test(is_true(false));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn is_true<I, N, L, E>(value: bool) -> IsTrue<(I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    IsTrue(value, PhantomData)
}

impl<I, N, L, E> SkipParserOnce<I, N, L, E> for IsTrue<(I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    #[inline]
    fn discard_once(self, _i: In<I, N, L, E>) -> Option<()> {
        self.0.then_some(())
    }
}

impl<I, N, L, E> ParserOnce<I, N, L, E> for IsTrue<(I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    type Out = ();
    #[inline]
    fn parse_once(self, _i: In<I, N, L, E>) -> Option<Self::Out> {
        self.0.then_some(())
    }
}

impl<I, N, L, E> SkipParserMut<I, N, L, E> for IsTrue<(I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    #[inline]
    fn discard_mut(&mut self, _i: In<I, N, L, E>) -> Option<()> {
        self.0.then_some(())
    }
}

impl<I, N, L, E> ParserMut<I, N, L, E> for IsTrue<(I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    #[inline]
    fn parse_mut(&mut self, _i: In<I, N, L, E>) -> Option<Self::Out> {
        self.0.then_some(())
    }
}

impl<I, N, L, E> SkipParser<I, N, L, E> for IsTrue<(I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    #[inline]
    fn discard(&self, _i: In<I, N, L, E>) -> Option<()> {
        self.0.then_some(())
    }
}

impl<I, N, L, E> Parser<I, N, L, E> for IsTrue<(I, N, L, E)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    #[inline]
    fn parse(&self, _i: In<I, N, L, E>) -> Option<Self::Out> {
        self.0.then_some(())
    }
}

/// Capture the consumed input as `SeqInput::Seq`.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ab".test(with_seq(item('a')));
/// assert_eq!(out, Some(('a', "a")));
/// ```
#[inline(always)]
pub fn with_seq<P>(parser: P) -> WithSeq<P> {
    WithSeq(parser)
}

pub struct WithSeq<P>(P);

impl<P, I, N, L, E> SkipParserOnce<I, N, L, E> for WithSeq<P>
where
    I: Input + SeqInput,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard_once(i)
    }
}

impl<P, I, N, L, E> SkipParserMut<I, N, L, E> for WithSeq<P>
where
    I: Input + SeqInput,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard_mut(i)
    }
}

impl<P, I, N, L, E> SkipParser<I, N, L, E> for WithSeq<P>
where
    I: Input + SeqInput,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard(i)
    }
}

impl<P, I, N, L, E, O> ParserOnce<I, N, L, E> for WithSeq<P>
where
    I: Input + SeqInput,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E, Out = O>,
{
    type Out = (O, I::Seq);
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        let cp0 = i.input.checkpoint();
        let out = self.0.parse_once(i.rb())?;
        let cp1 = i.input.checkpoint();
        let seq = I::seq(cp0, cp1);
        Some((out, seq))
    }
}

impl<P, I, N, L, E, O> ParserMut<I, N, L, E> for WithSeq<P>
where
    I: Input + SeqInput,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        let cp0 = i.input.checkpoint();
        let out = self.0.parse_mut(i.rb())?;
        let cp1 = i.input.checkpoint();
        let seq = I::seq(cp0, cp1);
        Some((out, seq))
    }
}

impl<P, I, N, L, E, O> Parser<I, N, L, E> for WithSeq<P>
where
    I: Input + SeqInput,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        let cp0 = i.input.checkpoint();
        let out = self.0.parse(i.rb())?;
        let cp1 = i.input.checkpoint();
        let seq = I::seq(cp0, cp1);
        Some((out, seq))
    }
}

/// Cut backtracking at the current position.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let parser = choice((right(cut, item('a')), item('b')));
/// let out = "a".test(parser);
/// assert_eq!(out, Some('a'));
///
/// let parser = choice((right(cut, item('a')), item('b')));
/// let out = "b".test(parser);
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn cut<I, N, L, E>(mut input: In<I, N, L, E>) -> Option<()>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    input.cut();
    Some(())
}

/// Run a parser without propagating `cut` to callers.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let parser = choice((right(uncut(cut), item('a')), item('b')));
/// let out = "b".test(parser);
/// assert_eq!(out, Some('b'));
/// ```
#[inline(always)]
pub fn uncut<P>(parser: P) -> Uncut<P> {
    Uncut(parser)
}

pub struct Uncut<P>(P);

#[inline]
fn run_uncut<I, N, L, E, O>(mut i: In<I, N, L, E>, f: impl FnOnce(In<I, N, L, E>) -> O) -> O
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    let mut is_cut = false;
    let is_cut = IsCut::non_root(&mut is_cut);
    let env = N::shorten_mut(&mut i.env);
    let local = L::shorten_mut(&mut i.local);
    let errors = E::shorten_mut(&mut i.errors);
    f(In {
        input: i.input,
        env,
        local,
        errors,
        is_cut,
    })
}

impl<P, I, N, L, E> SkipParserOnce<I, N, L, E> for Uncut<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        run_uncut(i, |i| self.0.discard_once(i))
    }
}

impl<P, I, N, L, E> SkipParserMut<I, N, L, E> for Uncut<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        run_uncut(i, |i| self.0.discard_mut(i))
    }
}

impl<P, I, N, L, E> SkipParser<I, N, L, E> for Uncut<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        run_uncut(i, |i| self.0.discard(i))
    }
}

impl<P, I, N, L, E> ParserOnce<I, N, L, E> for Uncut<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E>,
{
    type Out = P::Out;
    #[inline]
    fn parse_once(self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_uncut(i, |i| self.0.parse_once(i))
    }
}

impl<P, I, N, L, E> ParserMut<I, N, L, E> for Uncut<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_uncut(i, |i| self.0.parse_mut(i))
    }
}

impl<P, I, N, L, E> Parser<I, N, L, E> for Uncut<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_uncut(i, |i| self.0.parse(i))
    }
}

/// Cut only when the wrapped parser succeeds.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let parser = choice((right(cut_on_ok(item('a')), item('b')), item('b')));
/// let out = "ab".test(parser);
/// assert_eq!(out, Some('b'));
///
/// let parser = choice((right(cut_on_ok(item('a')), item('b')), item('b')));
/// let out = "b".test(parser);
/// assert_eq!(out, Some('b'));
///
/// let parser = choice((right(cut_on_ok(item('a')), item('b')), item('b')));
/// let out = "ac".test(parser);
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn cut_on_ok<P>(parser: P) -> CutIfOk<P> {
    CutIfOk(parser)
}

/// Cut after the wrapped parser succeeds.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let parser = choice((right(cut_after(item('a')), item('b')), item('b')));
/// let out = "ab".test(parser);
/// assert_eq!(out, Some('b'));
/// ```
#[inline(always)]
pub fn cut_after<P>(parser: P) -> CutIfOk<P> {
    CutIfOk(parser)
}

pub struct CutIfOk<P>(P);

impl<P, I, N, L, E> SkipParserOnce<I, N, L, E> for CutIfOk<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let out = self.0.discard_once(i.rb());
        if out.is_some() {
            i.cut();
        }
        out
    }
}

impl<P, I, N, L, E> SkipParserMut<I, N, L, E> for CutIfOk<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let out = self.0.discard_mut(i.rb());
        if out.is_some() {
            i.cut();
        }
        out
    }
}

impl<P, I, N, L, E> SkipParser<I, N, L, E> for CutIfOk<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let out = self.0.discard(i.rb());
        if out.is_some() {
            i.cut();
        }
        out
    }
}

impl<P, I, N, L, E> ParserOnce<I, N, L, E> for CutIfOk<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E>,
{
    type Out = P::Out;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        let out = self.0.parse_once(i.rb());
        if out.is_some() {
            i.cut();
        }
        out
    }
}

impl<P, I, N, L, E> ParserMut<I, N, L, E> for CutIfOk<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        let out = self.0.parse_mut(i.rb());
        if out.is_some() {
            i.cut();
        }
        out
    }
}

impl<P, I, N, L, E> Parser<I, N, L, E> for CutIfOk<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        let out = self.0.parse(i.rb());
        if out.is_some() {
            i.cut();
        }
        out
    }
}

/// Parse without consuming input.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let parser = seq(lookahead(item('a')), item('a'));
/// let out = "ab".test(parser);
/// assert_eq!(out, Some(('a', 'a')));
/// ```
#[inline(always)]
pub fn lookahead<P>(parser: P) -> Lookahead<P> {
    Lookahead(parser)
}

pub struct Lookahead<P>(P);

impl<P, I, N, L, E> SkipParserOnce<I, N, L, E> for Lookahead<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let errors_checkpoint = i.errors_checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.discard_once(i));
        if out.is_some() {
            i.errors_rollback(errors_checkpoint);
        }
        if out.is_some() || !is_cut {
            i.rollback(checkpoint);
        }
        out
    }
}

impl<P, I, N, L, E> SkipParserMut<I, N, L, E> for Lookahead<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let errors_checkpoint = i.errors_checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.discard_mut(i));
        if out.is_some() {
            i.errors_rollback(errors_checkpoint);
        }
        if out.is_some() || !is_cut {
            i.rollback(checkpoint);
        }
        out
    }
}

impl<P, I, N, L, E> SkipParser<I, N, L, E> for Lookahead<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let errors_checkpoint = i.errors_checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.discard(i));
        if out.is_some() {
            i.errors_rollback(errors_checkpoint);
        }
        if out.is_some() || !is_cut {
            i.rollback(checkpoint);
        }
        out
    }
}

impl<P, I, N, L, E, O> ParserOnce<I, N, L, E> for Lookahead<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E, Out = O>,
{
    type Out = O;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.lookahead(self.0)
    }
}

impl<P, I, N, L, E, O> ParserMut<I, N, L, E> for Lookahead<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.lookahead(self.0.by_mut())
    }
}

impl<P, I, N, L, E> Parser<I, N, L, E> for Lookahead<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.lookahead(self.0.by_ref())
    }
}

/// Succeed only if the parser fails.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let parser = seq(not(item('a')), item('b'));
/// let out = "bc".test(parser);
/// assert_eq!(out, Some(((), 'b')));
///
/// let out = "ac".test(parser);
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn not<P>(parser: P) -> Not<P> {
    Not(parser)
}

#[derive(Clone, Copy, Debug, Hash)]
pub struct Not<P>(P);

impl<P, I, N, L, E> SkipParserOnce<I, N, L, E> for Not<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        i.not(self.0)
    }
}

impl<P, I, N, L, E> SkipParserMut<I, N, L, E> for Not<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        i.not(self.0.by_mut())
    }
}

impl<P, I, N, L, E> SkipParser<I, N, L, E> for Not<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        i.not(self.0.by_ref())
    }
}

impl<P, I, N, L, E, O> ParserOnce<I, N, L, E> for Not<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E, Out = O>,
{
    type Out = ();
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.not(self.0)
    }
}

impl<P, I, N, L, E, O> ParserMut<I, N, L, E> for Not<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.not(self.0.by_mut())
    }
}

impl<P, I, N, L, E, O> Parser<I, N, L, E> for Not<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.not(self.0.by_ref())
    }
}

/// Parse an optional item.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ab".test(maybe(item('a')));
/// assert_eq!(out, Some(Some('a')));
///
/// let out = "bb".test(maybe(item('a')));
/// assert_eq!(out, Some(None));
/// ```
#[inline(always)]
pub fn maybe<P>(parser: P) -> OrNot<P> {
    OrNot(parser)
}

#[derive(Clone, Copy)]
pub struct OrNot<P>(P);

impl<P, I, N, L, E> SkipParserOnce<I, N, L, E> for OrNot<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let errors_checkpoint = i.errors_checkpoint();
        match i.capture_cut(|i| self.0.discard_once(i)) {
            (Some(_), _) => Some(()),
            (None, true) => None,
            (None, false) => {
                i.errors_rollback(errors_checkpoint);
                i.rollback(checkpoint);
                Some(())
            }
        }
    }
}

impl<P, I, N, L, E> SkipParserMut<I, N, L, E> for OrNot<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let errors_checkpoint = i.errors_checkpoint();
        match i.capture_cut(|i| self.0.discard_mut(i)) {
            (Some(_), _) => Some(()),
            (None, true) => None,
            (None, false) => {
                i.errors_rollback(errors_checkpoint);
                i.rollback(checkpoint);
                Some(())
            }
        }
    }
}

impl<P, I, N, L, E> SkipParser<I, N, L, E> for OrNot<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let errors_checkpoint = i.errors_checkpoint();
        match i.capture_cut(|i| self.0.discard(i)) {
            (Some(_), _) => Some(()),
            (None, true) => None,
            (None, false) => {
                i.errors_rollback(errors_checkpoint);
                i.rollback(checkpoint);
                Some(())
            }
        }
    }
}

impl<P, I, N, L, E, O> ParserOnce<I, N, L, E> for OrNot<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E, Out = O>,
{
    type Out = Option<O>;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.maybe(self.0)
    }
}

impl<P, I, N, L, E, O> ParserMut<I, N, L, E> for OrNot<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.maybe(self.0.by_mut())
    }
}

impl<P, I, N, L, E, O> Parser<I, N, L, E> for OrNot<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.maybe(self.0.by_ref())
    }
}

/// Attach a label to errors produced by the parser.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "a".test(label(item('a'), "a"));
/// assert_eq!(out, Some('a'));
///
/// let out = "b".test(label(item('a'), "a"));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn label<P>(parser: P, label: impl Into<Cow<'static, str>>) -> Label<P> {
    Label(parser, label.into())
}

pub struct Label<P>(P, Cow<'static, str>);

impl<P, I, N, L, E> SkipParserOnce<I, N, L, E> for Label<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
    crate::error::std::Expected<()>: Into<E::Error>,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        if self.0.discard_once(i.rb()).is_some() {
            return Some(());
        }
        let expected = crate::error::std::Expected::new(i.index(), self.1, ());
        let pos = i.pos();
        E::push(
            E::shorten_mut(&mut i.errors),
            pos.clone()..pos,
            expected.into(),
        );
        None
    }
}

impl<P, I, N, L, E> SkipParserMut<I, N, L, E> for Label<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
    crate::error::std::Expected<()>: Into<E::Error>,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        if self.0.discard_mut(i.rb()).is_some() {
            return Some(());
        }
        let expected = crate::error::std::Expected::new(i.index(), self.1.clone(), ());
        let pos = i.pos();
        E::push(
            E::shorten_mut(&mut i.errors),
            pos.clone()..pos,
            expected.into(),
        );
        None
    }
}

impl<P, I, N, L, E> SkipParser<I, N, L, E> for Label<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
    crate::error::std::Expected<()>: Into<E::Error>,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        if self.0.discard(i.rb()).is_some() {
            return Some(());
        }
        let expected = crate::error::std::Expected::new(i.index(), self.1.clone(), ());
        let pos = i.pos();
        E::push(
            E::shorten_mut(&mut i.errors),
            pos.clone()..pos,
            expected.into(),
        );
        None
    }
}

impl<P, I, N, L, E, O> ParserOnce<I, N, L, E> for Label<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E, Out = O>,
    crate::error::std::Expected<()>: Into<E::Error>,
{
    type Out = O;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.label(self.0, self.1)
    }
}

impl<P, I, N, L, E, O> ParserMut<I, N, L, E> for Label<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = O>,
    crate::error::std::Expected<()>: Into<E::Error>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.label(self.0.by_mut(), self.1.clone())
    }
}

impl<P, I, N, L, E, O> Parser<I, N, L, E> for Label<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = O>,
    crate::error::std::Expected<()>: Into<E::Error>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.label(self.0.by_ref(), self.1.clone())
    }
}

/// Like `label`, but builds the label lazily.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "a".test(label_with(item('a'), || "a"));
/// assert_eq!(out, Some('a'));
///
/// let out = "b".test(label_with(item('a'), || "a"));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn label_with<P, F, S>(parser: P, f: F) -> LabelWith<P, F>
where
    F: FnOnce() -> S,
    S: Into<Cow<'static, str>>,
{
    LabelWith { parser, f }
}

pub struct LabelWith<P, F> {
    parser: P,
    f: F,
}

impl<P, F, S, I, N, L, E> SkipParserOnce<I, N, L, E> for LabelWith<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
    F: FnOnce() -> S,
    S: Into<Cow<'static, str>>,
    crate::error::std::Expected<()>: Into<E::Error>,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        if self.parser.discard_once(i.rb()).is_some() {
            return Some(());
        }
        let expected = crate::error::std::Expected::new(i.index(), (self.f)(), ());
        let pos = i.pos();
        E::push(
            E::shorten_mut(&mut i.errors),
            pos.clone()..pos,
            expected.into(),
        );
        None
    }
}

impl<P, F, S, I, N, L, E> SkipParserMut<I, N, L, E> for LabelWith<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
    F: FnMut() -> S,
    S: Into<Cow<'static, str>>,
    crate::error::std::Expected<()>: Into<E::Error>,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        if self.parser.discard_mut(i.rb()).is_some() {
            return Some(());
        }
        let expected = crate::error::std::Expected::new(i.index(), (self.f)(), ());
        let pos = i.pos();
        E::push(
            E::shorten_mut(&mut i.errors),
            pos.clone()..pos,
            expected.into(),
        );
        None
    }
}

impl<P, F, S, I, N, L, E> SkipParser<I, N, L, E> for LabelWith<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
    F: Fn() -> S,
    S: Into<Cow<'static, str>>,
    crate::error::std::Expected<()>: Into<E::Error>,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        if self.parser.discard(i.rb()).is_some() {
            return Some(());
        }
        let expected = crate::error::std::Expected::new(i.index(), (self.f)(), ());
        let pos = i.pos();
        E::push(
            E::shorten_mut(&mut i.errors),
            pos.clone()..pos,
            expected.into(),
        );
        None
    }
}

impl<P, F, S, I, N, L, E, O> ParserOnce<I, N, L, E> for LabelWith<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E, Out = O>,
    F: FnOnce() -> S,
    S: Into<Cow<'static, str>>,
    crate::error::std::Expected<()>: Into<E::Error>,
{
    type Out = O;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.label_with(self.parser, self.f)
    }
}

impl<P, F, S, I, N, L, E, O> ParserMut<I, N, L, E> for LabelWith<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = O>,
    F: FnMut() -> S,
    S: Into<Cow<'static, str>>,
    crate::error::std::Expected<()>: Into<E::Error>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.label_with(self.parser.by_mut(), || (self.f)())
    }
}

impl<P, F, S, I, N, L, E, O> Parser<I, N, L, E> for LabelWith<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = O>,
    F: Fn() -> S,
    S: Into<Cow<'static, str>>,
    crate::error::std::Expected<()>: Into<E::Error>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.label_with(self.parser.by_ref(), || (self.f)())
    }
}

/// Attach a consumed range to the result.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "a".test(with_range(item('a')));
/// assert!(out.is_some());
///
/// let out = "b".test(with_range(item('a')));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn with_range<P>(parser: P) -> WithRange<P> {
    WithRange(parser)
}

pub struct WithRange<P>(P);

impl<P, I, N, L, E> SkipParserOnce<I, N, L, E> for WithRange<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard_once(i)
    }
}

impl<P, I, N, L, E> SkipParserMut<I, N, L, E> for WithRange<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard_mut(i)
    }
}

impl<P, I, N, L, E> SkipParser<I, N, L, E> for WithRange<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard(i)
    }
}

impl<P, I, N, L, E, O> ParserOnce<I, N, L, E> for WithRange<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E, Out = O>,
{
    type Out = (O, Range<I::Pos>);
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.with_range(self.0)
    }
}

impl<P, I, N, L, E, O> ParserMut<I, N, L, E> for WithRange<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.with_range(self.0.by_mut())
    }
}

impl<P, I, N, L, E, O> Parser<I, N, L, E> for WithRange<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.with_range(self.0.by_ref())
    }
}

/// Attach a consumed span to the result.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "a".test(with_span(item('a')));
/// assert!(out.is_some());
///
/// let out = "b".test(with_span(item('a')));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn with_span<P>(parser: P) -> WithSpan<P> {
    WithSpan(parser)
}

pub struct WithSpan<P>(P);

impl<P, I, N, L, E> SkipParserOnce<I, N, L, E> for WithSpan<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard_once(i)
    }
}

impl<P, I, N, L, E> SkipParserMut<I, N, L, E> for WithSpan<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard_mut(i)
    }
}

impl<P, I, N, L, E> SkipParser<I, N, L, E> for WithSpan<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.0.discard(i)
    }
}

impl<P, I, N, L, E, O> ParserOnce<I, N, L, E> for WithSpan<P>
where
    I: Input,
    I::Pos: ToSpan,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E, Out = O>,
{
    type Out = (O, <I::Pos as ToSpan>::Span);
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.with_span(self.0)
    }
}

impl<P, I, N, L, E, O> ParserMut<I, N, L, E> for WithSpan<P>
where
    I: Input,
    I::Pos: ToSpan,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.with_span(self.0.by_mut())
    }
}

impl<P, I, N, L, E, O> Parser<I, N, L, E> for WithSpan<P>
where
    I: Input,
    I::Pos: ToSpan,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        i.with_span(self.0.by_ref())
    }
}

pub struct SetEnv<'a, P, N1, N2: Reborrow + 'a>(P, N2::Target<'a>, PhantomData<fn() -> N1>);

#[inline(always)]
pub fn set_env<'a, P, N1, N2: Reborrowed<'a>>(parser: P, env: N2) -> SetEnv<'a, P, N1, N2> {
    SetEnv(parser, env, PhantomData)
}

impl<'a, P, I, N1, N2, L, E> SkipParserOnce<I, N1, L, E> for SetEnv<'a, P, N1, N2>
where
    I: Input,
    N1: Reborrow,
    N2: Reborrow + 'a,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N2, L, E>,
{
    #[inline]
    fn discard_once(
        self,
        In {
            input,
            env: _,
            local,
            errors,
            is_cut,
        }: In<I, N1, L, E>,
    ) -> Option<()> {
        self.0.discard_once(In {
            input,
            env: N2::shorten(self.1),
            local: L::shorten(local),
            errors: E::shorten(errors),
            is_cut: IsCut::shorten(is_cut),
        })
    }
}

impl<'a, P, I, N1, N2, L, E> SkipParserMut<I, N1, L, E> for SetEnv<'a, P, N1, N2>
where
    I: Input,
    N1: Reborrow,
    N2: Reborrow + 'a,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N2, L, E>,
{
    #[inline]
    fn discard_mut(
        &mut self,
        In {
            input,
            env: _,
            local,
            errors,
            is_cut,
        }: In<I, N1, L, E>,
    ) -> Option<()> {
        self.0.discard_mut(In {
            input,
            env: N2::shorten_mut(&mut self.1),
            local: L::shorten(local),
            errors: E::shorten(errors),
            is_cut: IsCut::shorten(is_cut),
        })
    }
}

impl<'a, P, I, N1, N2, L, E> SkipParser<I, N1, L, E> for SetEnv<'a, P, N1, N2>
where
    I: Input,
    N1: Reborrow,
    N2: Reborrow + 'a,
    N2::Target<'a>: Copy,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N2, L, E>,
{
    #[inline]
    fn discard(
        &self,
        In {
            input,
            env: _,
            local,
            errors,
            is_cut,
        }: In<I, N1, L, E>,
    ) -> Option<()> {
        self.0.discard(In {
            input,
            env: N2::shorten(self.1),
            local: L::shorten(local),
            errors: E::shorten(errors),
            is_cut: IsCut::shorten(is_cut),
        })
    }
}

impl<'a, P, I, N1, N2, L, E> ParserOnce<I, N1, L, E> for SetEnv<'a, P, N1, N2>
where
    I: Input,
    N1: Reborrow,
    N2: Reborrow + 'a,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N2, L, E>,
{
    type Out = P::Out;
    #[inline]
    fn parse_once(
        self,
        In {
            input,
            env: _,
            local,
            errors,
            is_cut,
        }: In<I, N1, L, E>,
    ) -> Option<Self::Out> {
        self.0.parse_once(In {
            input,
            env: N2::shorten(self.1),
            local: L::shorten(local),
            errors: E::shorten(errors),
            is_cut: IsCut::shorten(is_cut),
        })
    }
}

impl<'a, P, I, N1, N2, L, E> ParserMut<I, N1, L, E> for SetEnv<'a, P, N1, N2>
where
    I: Input,
    N1: Reborrow,
    N2: Reborrow + 'a,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N2, L, E>,
{
    #[inline]
    fn parse_mut(
        &mut self,
        In {
            input,
            env: _,
            local,
            errors,
            is_cut,
        }: In<I, N1, L, E>,
    ) -> Option<Self::Out> {
        self.0.parse_mut(In {
            input,
            env: N2::shorten_mut(&mut self.1),
            local: L::shorten(local),
            errors: E::shorten(errors),
            is_cut: IsCut::shorten(is_cut),
        })
    }
}

impl<'a, P, I, N1, N2, L, E> Parser<I, N1, L, E> for SetEnv<'a, P, N1, N2>
where
    I: Input,
    N1: Reborrow,
    N2: Reborrow + 'a,
    N2::Target<'a>: Copy,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N2, L, E>,
{
    #[inline]
    fn parse(
        &self,
        In {
            input,
            env: _,
            local,
            errors,
            is_cut,
        }: In<I, N1, L, E>,
    ) -> Option<Self::Out> {
        self.0.parse(In {
            input,
            env: N2::shorten(self.1),
            local: L::shorten(local),
            errors: E::shorten(errors),
            is_cut: IsCut::shorten(is_cut),
        })
    }
}

pub struct SetLocal<'a, P, L2: RbBack + 'a>(P, L2::Target<'a>, PhantomData<fn() -> ()>);

#[inline(always)]
pub fn set_local<'a, P, L2: Reborrowed<'a> + RbBack>(parser: P, local: L2) -> SetLocal<'a, P, L2> {
    SetLocal(parser, local, PhantomData)
}

impl<'a, P, I, N, L1, L2, E> SkipParserOnce<I, N, L1, E> for SetLocal<'a, P, L2>
where
    I: Input,
    N: Reborrow,
    L1: RbBack,
    L2: RbBack + 'a,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L2, E>,
{
    #[inline]
    fn discard_once(
        self,
        In {
            input,
            env,
            local: _,
            errors,
            is_cut,
        }: In<I, N, L1, E>,
    ) -> Option<()> {
        self.0.discard_once(In {
            input,
            env: N::shorten(env),
            local: L2::shorten(self.1),
            errors: E::shorten(errors),
            is_cut: IsCut::shorten(is_cut),
        })
    }
}

impl<'a, P, I, N, L1, L2, E> SkipParserMut<I, N, L1, E> for SetLocal<'a, P, L2>
where
    I: Input,
    N: Reborrow,
    L1: RbBack,
    L2: RbBack + 'a,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L2, E>,
{
    #[inline]
    fn discard_mut(
        &mut self,
        In {
            input,
            env,
            local: _,
            errors,
            is_cut,
        }: In<I, N, L1, E>,
    ) -> Option<()> {
        self.0.discard_mut(In {
            input,
            env: N::shorten(env),
            local: L2::shorten_mut(&mut self.1),
            errors: E::shorten(errors),
            is_cut: IsCut::shorten(is_cut),
        })
    }
}

impl<'a, P, I, N, L1, L2, E> SkipParser<I, N, L1, E> for SetLocal<'a, P, L2>
where
    I: Input,
    N: Reborrow,
    L1: RbBack,
    L2: RbBack + 'a,
    L2::Target<'a>: Copy,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L2, E>,
{
    #[inline]
    fn discard(
        &self,
        In {
            input,
            env,
            local: _,
            errors,
            is_cut,
        }: In<I, N, L1, E>,
    ) -> Option<()> {
        self.0.discard(In {
            input,
            env: N::shorten(env),
            local: L2::shorten(self.1),
            errors: E::shorten(errors),
            is_cut: IsCut::shorten(is_cut),
        })
    }
}

impl<'a, P, I, N, L1, L2, E> ParserOnce<I, N, L1, E> for SetLocal<'a, P, L2>
where
    I: Input,
    N: Reborrow,
    L1: RbBack,
    L2: RbBack + 'a,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L2, E>,
{
    type Out = P::Out;
    #[inline]
    fn parse_once(
        self,
        In {
            input,
            env,
            local: _,
            errors,
            is_cut,
        }: In<I, N, L1, E>,
    ) -> Option<Self::Out> {
        self.0.parse_once(In {
            input,
            env: N::shorten(env),
            local: L2::shorten(self.1),
            errors: E::shorten(errors),
            is_cut: IsCut::shorten(is_cut),
        })
    }
}

impl<'a, P, I, N, L1, L2, E> ParserMut<I, N, L1, E> for SetLocal<'a, P, L2>
where
    I: Input,
    N: Reborrow,
    L1: RbBack,
    L2: RbBack + 'a,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L2, E>,
{
    #[inline]
    fn parse_mut(
        &mut self,
        In {
            input,
            env,
            local: _,
            errors,
            is_cut,
        }: In<I, N, L1, E>,
    ) -> Option<Self::Out> {
        self.0.parse_mut(In {
            input,
            env: N::shorten(env),
            local: L2::shorten_mut(&mut self.1),
            errors: E::shorten(errors),
            is_cut: IsCut::shorten(is_cut),
        })
    }
}

impl<'a, P, I, N, L1, L2, E> Parser<I, N, L1, E> for SetLocal<'a, P, L2>
where
    I: Input,
    N: Reborrow,
    L1: RbBack,
    L2: RbBack + 'a,
    L2::Target<'a>: Copy,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L2, E>,
{
    #[inline]
    fn parse(
        &self,
        In {
            input,
            env,
            local: _,
            errors,
            is_cut,
        }: In<I, N, L1, E>,
    ) -> Option<Self::Out> {
        self.0.parse(In {
            input,
            env: N::shorten(env),
            local: L2::shorten(self.1),
            errors: E::shorten(errors),
            is_cut: IsCut::shorten(is_cut),
        })
    }
}

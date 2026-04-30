use core::marker::PhantomData;
use core::ops::ControlFlow;

use reborrow_generic::Reborrow;

use crate::back::RbBack;
use crate::error::ErrorSink;
use crate::input::{In, Input};
use crate::parser::prim::RefOrMutParser;
use crate::parser::{Parser, ParserMut, ParserOnce, SkipParser, SkipParserMut, SkipParserOnce};

#[inline]
fn maybe<P, I, N, L, E, O>(i: &mut In<I, N, L, E>, parser: &mut P) -> Option<Option<O>>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = O>,
{
    i.maybe(parser.by_mut())
}

pub struct Flow<P, S, Step>(pub P, pub S, pub Step);

impl<P, S, Step> Flow<P, S, Step> {
    #[inline]
    pub fn new(parser: P, state: S, step: Step) -> Self {
        Self(parser, state, step)
    }
}

/// Build a flow parser that loops until the step returns `Break`.
///
/// ```rust
/// use chasa::prelude::*;
/// use std::ops::ControlFlow;
///
/// let parser = flow(any, 0usize, |n, c| {
///     if c == 'b' {
///         ControlFlow::Break(n)
///     } else {
///         ControlFlow::Continue(n + 1)
///     }
/// });
/// let out = "aaab".test(parser);
/// assert_eq!(out, Some(3));
///
/// let parser = flow(any, 0usize, |n, _| ControlFlow::<(), _>::Continue(n + 1));
/// let out = "".test(parser);
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn flow<P, S, Step>(parser: P, state: S, step: Step) -> Flow<P, S, Step> {
    Flow(parser, state, step)
}

impl<I, N, L, E, P, S, Step, C> SkipParserOnce<I, N, L, E> for Flow<P, S, Step>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Step: FnMut(S, P::Out) -> ControlFlow<C, S>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_once(i).map(|_| ())
    }
}

impl<I, N, L, E, P, S, Step, C> SkipParserMut<I, N, L, E> for Flow<P, S, Step>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    S: Clone,
    Step: FnMut(S, P::Out) -> ControlFlow<C, S>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_mut(i).map(|_| ())
    }
}

impl<I, N, L, E, P, S, Step, C> SkipParser<I, N, L, E> for Flow<P, S, Step>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    S: Clone,
    Step: Fn(S, P::Out) -> ControlFlow<C, S>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.parse(i).map(|_| ())
    }
}

impl<I, N, L, E, P, S, Step, C> ParserOnce<I, N, L, E> for Flow<P, S, Step>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Step: FnMut(S, P::Out) -> ControlFlow<C, S>,
{
    type Out = C;
    #[inline]
    fn parse_once(self, mut input: In<I, N, L, E>) -> Option<C> {
        let Flow(mut parser, mut state, mut step) = self;
        loop {
            let value = parser.parse_mut(input.rb())?;
            match step(state, value) {
                ControlFlow::Continue(next) => state = next,
                ControlFlow::Break(out) => return Some(out),
            }
        }
    }
}

impl<I, N, L, E, P, S, Step, C> ParserMut<I, N, L, E> for Flow<P, S, Step>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    S: Clone,
    Step: FnMut(S, P::Out) -> ControlFlow<C, S>,
{
    #[inline]
    fn parse_mut(&mut self, mut input: In<I, N, L, E>) -> Option<C> {
        let mut parser = RefOrMutParser::new_mut(&mut self.0);
        let mut state = self.1.clone();
        let step = &mut self.2;
        loop {
            let value = parser.parse_mut(input.rb())?;
            match step(state, value) {
                ControlFlow::Continue(next) => state = next,
                ControlFlow::Break(out) => return Some(out),
            }
        }
    }
}

impl<I, N, L, E, P, S, Step, C> Parser<I, N, L, E> for Flow<P, S, Step>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    S: Clone,
    Step: Fn(S, P::Out) -> ControlFlow<C, S>,
{
    #[inline]
    fn parse(&self, mut input: In<I, N, L, E>) -> Option<C> {
        let mut parser = RefOrMutParser::new_ref(&self.0);
        let mut state = self.1.clone();
        let step = &self.2;
        loop {
            let value = parser.parse_mut(input.rb())?;
            match step(state, value) {
                ControlFlow::Continue(next) => state = next,
                ControlFlow::Break(out) => return Some(out),
            }
        }
    }
}

pub struct RawFlowManyIterator<'a, P, I, N, L, E, C, B>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    pub(crate) parser: P,
    pub(crate) input: In<'a, I, N, L, E>,
    pub(crate) done: bool,
    pub(crate) break_: &'a mut Option<B>,
    pub(crate) hard_failure: &'a mut bool,
    pub(crate) _phantom: PhantomData<fn() -> C>,
}

pub type FlowManyIterator<'a, 'b, P, I, N, L, E, C, B> =
    RawFlowManyIterator<'a, RefOrMutParser<'b, P, I, N, L, E>, I, N, L, E, C, B>;

impl<'a, P, I, N, L, E, C, B> Iterator for RawFlowManyIterator<'a, P, I, N, L, E, C, B>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = ControlFlow<B, C>>,
{
    type Item = C;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.done || *self.hard_failure {
            return None;
        }
        match self.parser.parse_mut(self.input.rb()) {
            Some(ControlFlow::Continue(v)) => Some(v),
            Some(ControlFlow::Break(b)) => {
                self.done = true;
                *self.break_ = Some(b);
                None
            }
            None => {
                *self.hard_failure = true;
                self.done = true;
                None
            }
        }
    }
}

pub struct FlowMany<P, O>(pub P, PhantomData<fn() -> O>);

impl<P, O> FlowMany<P, O> {
    #[inline]
    pub fn new(parser: P) -> Self {
        Self(parser, PhantomData)
    }
}

/// Build a `flow_many` parser that collects `Continue` values.
///
/// ```rust
/// use chasa::prelude::*;
/// use std::ops::ControlFlow;
///
/// let take = choice((
///     map(item(']'), ControlFlow::Break),
///     map(any, ControlFlow::Continue),
/// ));
/// let out: Option<(String, Option<char>)> =
///     "ab]".test(flow_many(take));
/// assert_eq!(out, Some(("ab".to_string(), Some(']'))));
///
/// let take = map(item('a'), ControlFlow::Continue);
/// let out: Option<(String, Option<char>)> =
///     "".test(flow_many(take));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn flow_many<P, O>(parser: P) -> FlowMany<P, O> {
    FlowMany(parser, PhantomData)
}

pub struct RawManyTillIterator<'a, P, Q, I, N, L, E, C, B>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    pub(crate) parser: P,
    pub(crate) till: Q,
    pub(crate) input: In<'a, I, N, L, E>,
    pub(crate) done: bool,
    pub(crate) break_: &'a mut Option<B>,
    pub(crate) hard_failure: &'a mut bool,
    pub(crate) _phantom: PhantomData<fn() -> C>,
}

pub type ManyTillIterator<'a, 'b, 'c, P, Q, I, N, L, E, C, B> = RawManyTillIterator<
    'a,
    RefOrMutParser<'b, P, I, N, L, E>,
    RefOrMutParser<'c, Q, I, N, L, E>,
    I,
    N,
    L,
    E,
    C,
    B,
>;

impl<'a, P, Q, I, N, L, E, C, B> Iterator for RawManyTillIterator<'a, P, Q, I, N, L, E, C, B>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = C>,
    Q: ParserMut<I, N, L, E, Out = B>,
{
    type Item = C;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.done || *self.hard_failure {
            return None;
        }
        match maybe(&mut self.input, &mut self.till) {
            Some(Some(b)) => {
                self.done = true;
                *self.break_ = Some(b);
                None
            }
            Some(None) => match self.parser.parse_mut(self.input.rb()) {
                Some(v) => Some(v),
                None => {
                    *self.hard_failure = true;
                    self.done = true;
                    None
                }
            },
            None => {
                *self.hard_failure = true;
                self.done = true;
                None
            }
        }
    }
}

pub struct ManyTill<P, Q, O>(pub P, pub Q, PhantomData<fn() -> O>);

impl<P, Q, O> ManyTill<P, Q, O> {
    #[inline]
    pub fn new(parser: P, till: Q) -> Self {
        Self(parser, till, PhantomData)
    }
}

/// Parse zero or more items until `till` succeeds, returning both.
///
/// `till` is tried before each item with rollback on failure.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out: Option<(String, char)> = "ab]".test(many_till(any, item(']')));
/// assert_eq!(out, Some(("ab".to_string(), ']')));
///
/// let out: Option<(String, char)> = "]".test(many_till(any, item(']')));
/// assert_eq!(out, Some(("".to_string(), ']')));
///
/// let out: Option<(String, char)> = "ab".test(many_till(any, item(']')));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn many_till<P, Q, O>(parser: P, till: Q) -> ManyTill<P, Q, O> {
    ManyTill::new(parser, till)
}

impl<I, N, L, E, P, O, C, B> SkipParserOnce<I, N, L, E> for FlowMany<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = ControlFlow<B, C>>,
    O: FromIterator<C>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_once(i).map(|_| ())
    }
}

impl<I, N, L, E, P, Q, O, C, B> SkipParserOnce<I, N, L, E> for ManyTill<P, Q, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = C>,
    Q: ParserMut<I, N, L, E, Out = B>,
    O: FromIterator<C>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_once(i).map(|_| ())
    }
}

impl<I, N, L, E, P, Q, O, C, B> SkipParserMut<I, N, L, E> for ManyTill<P, Q, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = C>,
    Q: ParserMut<I, N, L, E, Out = B>,
    O: FromIterator<C>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_mut(i).map(|_| ())
    }
}

impl<I, N, L, E, P, Q, O, C, B> SkipParser<I, N, L, E> for ManyTill<P, Q, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = C>,
    Q: Parser<I, N, L, E, Out = B>,
    O: FromIterator<C>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.parse(i).map(|_| ())
    }
}

impl<I, N, L, E, P, Q, O, C, B> ParserOnce<I, N, L, E> for ManyTill<P, Q, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = C>,
    Q: ParserMut<I, N, L, E, Out = B>,
    O: FromIterator<C>,
{
    type Out = (O, B);

    #[inline]
    fn parse_once(self, mut input: In<I, N, L, E>) -> Option<(O, B)> {
        let mut hard_failure = false;
        let mut break_ = None;
        let it = RawManyTillIterator {
            parser: self.0,
            till: self.1,
            input: input.rb(),
            done: false,
            break_: &mut break_,
            hard_failure: &mut hard_failure,
            _phantom: PhantomData,
        };
        let out: O = it.collect();
        if hard_failure {
            None
        } else {
            Some((out, break_?))
        }
    }
}

impl<I, N, L, E, P, Q, O, C, B> ParserMut<I, N, L, E> for ManyTill<P, Q, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = C>,
    Q: ParserMut<I, N, L, E, Out = B>,
    O: FromIterator<C>,
{
    #[inline]
    fn parse_mut(&mut self, mut input: In<I, N, L, E>) -> Option<(O, B)> {
        let mut hard_failure = false;
        let mut break_ = None;
        let it = RawManyTillIterator {
            parser: RefOrMutParser::new_mut(&mut self.0),
            till: RefOrMutParser::new_mut(&mut self.1),
            input: input.rb(),
            done: false,
            break_: &mut break_,
            hard_failure: &mut hard_failure,
            _phantom: PhantomData,
        };
        let out: O = it.collect();
        if hard_failure {
            None
        } else {
            Some((out, break_?))
        }
    }
}

impl<I, N, L, E, P, Q, O, C, B> Parser<I, N, L, E> for ManyTill<P, Q, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = C>,
    Q: Parser<I, N, L, E, Out = B>,
    O: FromIterator<C>,
{
    #[inline]
    fn parse(&self, mut input: In<I, N, L, E>) -> Option<(O, B)> {
        let mut hard_failure = false;
        let mut break_ = None;
        let it = RawManyTillIterator {
            parser: RefOrMutParser::new_ref(&self.0),
            till: RefOrMutParser::new_ref(&self.1),
            input: input.rb(),
            done: false,
            break_: &mut break_,
            hard_failure: &mut hard_failure,
            _phantom: PhantomData,
        };
        let out: O = it.collect();
        if hard_failure {
            None
        } else {
            Some((out, break_?))
        }
    }
}

impl<I, N, L, E, P, O, C, B> SkipParserMut<I, N, L, E> for FlowMany<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = ControlFlow<B, C>>,
    O: FromIterator<C>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_mut(i).map(|_| ())
    }
}

impl<I, N, L, E, P, O, C, B> SkipParser<I, N, L, E> for FlowMany<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = ControlFlow<B, C>>,
    O: FromIterator<C>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.parse(i).map(|_| ())
    }
}

impl<I, N, L, E, P, O, C, B> ParserOnce<I, N, L, E> for FlowMany<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = ControlFlow<B, C>>,
    O: FromIterator<C>,
{
    type Out = (O, Option<B>);

    #[inline]
    fn parse_once(self, mut input: In<I, N, L, E>) -> Option<(O, Option<B>)> {
        let mut hard_failure = false;
        let mut break_ = None;
        let it = RawFlowManyIterator {
            parser: self.0,
            input: input.rb(),
            done: false,
            break_: &mut break_,
            hard_failure: &mut hard_failure,
            _phantom: PhantomData,
        };
        let out: O = it.collect();
        if hard_failure {
            None
        } else {
            Some((out, break_))
        }
    }
}

impl<I, N, L, E, P, O, C, B> ParserMut<I, N, L, E> for FlowMany<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = ControlFlow<B, C>>,
    O: FromIterator<C>,
{
    #[inline]
    fn parse_mut(&mut self, mut input: In<I, N, L, E>) -> Option<(O, Option<B>)> {
        let mut hard_failure = false;
        let mut break_ = None;
        let it = RawFlowManyIterator {
            parser: RefOrMutParser::new_mut(&mut self.0),
            input: input.rb(),
            done: false,
            break_: &mut break_,
            hard_failure: &mut hard_failure,
            _phantom: PhantomData,
        };
        let out: O = it.collect();
        if hard_failure {
            None
        } else {
            Some((out, break_))
        }
    }
}

impl<I, N, L, E, P, O, C, B> Parser<I, N, L, E> for FlowMany<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = ControlFlow<B, C>>,
    O: FromIterator<C>,
{
    #[inline]
    fn parse(&self, mut input: In<I, N, L, E>) -> Option<(O, Option<B>)> {
        let mut hard_failure = false;
        let mut break_ = None;
        let it = RawFlowManyIterator {
            parser: RefOrMutParser::new_ref(&self.0),
            input: input.rb(),
            done: false,
            break_: &mut break_,
            hard_failure: &mut hard_failure,
            _phantom: PhantomData,
        };
        let out: O = it.collect();
        if hard_failure {
            None
        } else {
            Some((out, break_))
        }
    }
}

pub struct FlowManyMap<P, F>(pub P, pub F);

/// Build a `flow_many_map` parser that maps the iterator.
///
/// ```rust
/// use chasa::prelude::*;
/// use chasa::parser::flow::FlowManyIterator;
/// use std::ops::ControlFlow;
///
/// let take = choice((
///     map(item(']'), ControlFlow::Break),
///     map(any, ControlFlow::Continue),
/// ));
/// let out = "ab]".test(flow_many_map(
///     take,
///     |it: FlowManyIterator<'_, '_, _, _, _, _, _, _, _>| it.count(),
/// ));
/// assert_eq!(out, Some((2, Some(']'))));
///
/// let out =
///     "".test(flow_many_map(take, |it: FlowManyIterator<'_, '_, _, _, _, _, _, _, _>| {
///         it.count()
///     }));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn flow_many_map_once<P, F>(parser: P, f: F) -> FlowManyMap<P, F> {
    FlowManyMap(parser, f)
}

#[inline(always)]
pub fn flow_many_map_mut<P, F>(parser: P, f: F) -> FlowManyMap<P, F> {
    FlowManyMap(parser, f)
}

/// Build a `flow_many_map` parser that maps the iterator.
///
/// ```rust
/// use chasa::prelude::*;
/// use chasa::parser::flow::FlowManyIterator;
/// use std::ops::ControlFlow;
///
/// let take = choice((
///     map(item(']'), ControlFlow::Break),
///     map(any, ControlFlow::Continue),
/// ));
/// let out = "ab]".test(flow_many_map(
///     take,
///     |it: FlowManyIterator<'_, '_, _, _, _, _, _, _, _>| it.count(),
/// ));
/// assert_eq!(out, Some((2, Some(']'))));
///
/// let out =
///     "".test(flow_many_map(take, |it: FlowManyIterator<'_, '_, _, _, _, _, _, _, _>| {
///         it.count()
///     }));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn flow_many_map<P, F>(parser: P, f: F) -> FlowManyMap<P, F> {
    FlowManyMap(parser, f)
}

impl<I, N, L, E, P, F, O, C, B> SkipParserOnce<I, N, L, E> for FlowManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = ControlFlow<B, C>>,
    F: for<'a, 'b> FnOnce(FlowManyIterator<'a, 'b, P, I, N, L, E, C, B>) -> O,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_once(i).map(|_| ())
    }
}

impl<I, N, L, E, P, F, O, C, B> SkipParserMut<I, N, L, E> for FlowManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = ControlFlow<B, C>>,
    F: for<'a, 'b> FnMut(FlowManyIterator<'a, 'b, P, I, N, L, E, C, B>) -> O,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_mut(i).map(|_| ())
    }
}

impl<I, N, L, E, P, F, O, C, B> SkipParser<I, N, L, E> for FlowManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = ControlFlow<B, C>>,
    F: for<'a, 'b> Fn(FlowManyIterator<'a, 'b, P, I, N, L, E, C, B>) -> O,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.parse(i).map(|_| ())
    }
}

impl<I, N, L, E, P, F, O, C, B> ParserOnce<I, N, L, E> for FlowManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = ControlFlow<B, C>>,
    F: for<'a, 'b> FnOnce(FlowManyIterator<'a, 'b, P, I, N, L, E, C, B>) -> O,
{
    type Out = (O, Option<B>);

    #[inline]
    fn parse_once(self, mut input: In<I, N, L, E>) -> Option<(O, Option<B>)> {
        let FlowManyMap(mut parser, f) = self;
        let mut hard_failure = false;
        let mut break_ = None;
        let it = RawFlowManyIterator {
            parser: RefOrMutParser::new_mut(&mut parser),
            input: input.rb(),
            done: false,
            break_: &mut break_,
            hard_failure: &mut hard_failure,
            _phantom: PhantomData,
        };
        let out = f(it);
        if hard_failure {
            None
        } else {
            Some((out, break_))
        }
    }
}

impl<I, N, L, E, P, F, O, C, B> ParserMut<I, N, L, E> for FlowManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = ControlFlow<B, C>>,
    F: for<'a, 'b> FnMut(FlowManyIterator<'a, 'b, P, I, N, L, E, C, B>) -> O,
{
    #[inline]
    fn parse_mut(&mut self, mut input: In<I, N, L, E>) -> Option<(O, Option<B>)> {
        let mut hard_failure = false;
        let mut break_ = None;
        let it = RawFlowManyIterator {
            parser: RefOrMutParser::new_mut(&mut self.0),
            input: input.rb(),
            done: false,
            break_: &mut break_,
            hard_failure: &mut hard_failure,
            _phantom: PhantomData,
        };
        let out = (self.1)(it);
        if hard_failure {
            None
        } else {
            Some((out, break_))
        }
    }
}

impl<I, N, L, E, P, F, O, C, B> Parser<I, N, L, E> for FlowManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = ControlFlow<B, C>>,
    F: for<'a, 'b> Fn(FlowManyIterator<'a, 'b, P, I, N, L, E, C, B>) -> O,
{
    #[inline]
    fn parse(&self, mut input: In<I, N, L, E>) -> Option<(O, Option<B>)> {
        let mut hard_failure = false;
        let mut break_ = None;
        let it = RawFlowManyIterator {
            parser: RefOrMutParser::new_ref(&self.0),
            input: input.rb(),
            done: false,
            break_: &mut break_,
            hard_failure: &mut hard_failure,
            _phantom: PhantomData,
        };
        let out = (self.1)(it);
        if hard_failure {
            None
        } else {
            Some((out, break_))
        }
    }
}

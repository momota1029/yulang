//! Parser traits and extension methods.
//!
//! ```rust
//! use chasa::prelude::*;
//!
//! let parser = item('a').map(|c| c.to_ascii_uppercase());
//! let out = "a".test(parser);
//! assert_eq!(out, Some('A'));
//!
//! let out = "b".test(item('a'));
//! assert_eq!(out, None);
//! ```

use std::ops::ControlFlow;

use reborrow_generic::{Reborrow, Reborrowed};

use crate::error::std::StdErr;
use crate::input::{In, SeqInput, ToSpan};
use crate::{ErrorSink, Input, LatestSink, RbBack};

pub mod chain;
pub mod choice;
pub mod flow;
pub mod item;
pub mod many;
pub mod memo;
pub mod prim;
pub mod sep;
pub mod str;
pub mod then;
pub mod token;
pub mod trie;

pub trait SkipParserOnce<
    I: Input,
    N: Reborrow = (),
    L: RbBack = (),
    E: ErrorSink<I::Pos> = LatestSink<<I as Input>::Pos, StdErr<<I as Input>::Item>>,
>
{
    /// Run a parser and discard its output.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    /// use chasa::input::IsCut;
    /// use chasa::LatestSink;
    ///
    /// let mut input = "a";
    /// let mut errors = LatestSink::new();
    /// let mut is_cut = false;
    /// let out = item('a').discard_once(In::new(&mut input, &mut errors, IsCut::new(&mut is_cut)));
    /// assert_eq!(out, Some(()));
    /// ```
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()>;

    /// Build a sequential parser tuple.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').seq(item('b'));
    /// let out = "ab".test(parser);
    /// assert_eq!(out, Some(('a', 'b')));
    /// ```
    #[inline(always)]
    fn seq<P>(self, right: P) -> (Self, P)
    where
        Self: Sized,
    {
        then::seq(self, right)
    }

    /// Run a parser with a fixed environment.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').set_env::<()>(());
    /// let out = "a".test(parser);
    /// assert_eq!(out, Some('a'));
    /// ```
    #[inline(always)]
    fn set_env<'a, N1>(self, env: N) -> prim::SetEnv<'a, Self, N1, N>
    where
        Self: Sized,
        N: Reborrowed<'a>,
    {
        prim::set_env(self, env)
    }

    /// Run a parser with a fixed local state.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').set_local(());
    /// let out = "a".test(parser);
    /// assert_eq!(out, Some('a'));
    /// ```
    #[inline(always)]
    fn set_local<'a>(self, local: L) -> prim::SetLocal<'a, Self, L>
    where
        Self: Sized,
        L: Reborrowed<'a> + RbBack,
    {
        prim::set_local(self, local)
    }

    /// Parse without consuming input on success.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let mut input = "ab";
    /// let out = input.test(item('a').lookahead());
    /// assert_eq!(out, Some('a'));
    /// let out = input.test(item('a'));
    /// assert_eq!(out, Some('a'));
    /// ```
    #[inline(always)]
    fn lookahead(self) -> prim::Lookahead<Self>
    where
        Self: Sized,
    {
        prim::lookahead(self)
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
    fn uncut(self) -> prim::Uncut<Self>
    where
        Self: Sized,
    {
        prim::uncut(self)
    }

    /// Cut backtracking when the parser succeeds.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let out = "a".test(item('a').cut_on_ok());
    /// assert_eq!(out, Some('a'));
    /// ```
    #[inline(always)]
    fn cut_on_ok(self) -> prim::CutIfOk<Self>
    where
        Self: Sized,
    {
        prim::cut_on_ok(self)
    }

    /// Make a parser optional.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let out = "b".test(item('a').or_not());
    /// assert_eq!(out, Some(None));
    /// ```
    #[inline(always)]
    fn or_not(self) -> prim::OrNot<Self>
    where
        Self: Sized,
    {
        prim::maybe(self)
    }

    /// Sequence two parsers and return the left output.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let out = "ab".test(item('a').left(item('b')));
    /// assert_eq!(out, Some('a'));
    /// ```
    #[inline(always)]
    fn left<P>(self, right: P) -> then::Left<Self, P>
    where
        Self: Sized,
    {
        then::left(self, right)
    }

    /// Sequence two parsers and return the right output.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let out = "ab".test(item('a').right(item('b')));
    /// assert_eq!(out, Some('b'));
    /// ```
    #[inline(always)]
    fn right<P>(self, right: P) -> then::Right<Self, P>
    where
        Self: Sized,
    {
        then::right(self, right)
    }

    /// Parse a value between two parsers.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').between(item('('), item(')'));
    /// let out = "(a)".test(parser);
    /// assert_eq!(out, Some('a'));
    /// ```
    #[inline(always)]
    fn between<P, Q>(self, left: P, right: Q) -> then::Between<P, Self, Q>
    where
        Self: Sized,
        P: SkipParserOnce<I, N, L, E>,
        Q: SkipParserOnce<I, N, L, E>,
    {
        then::between(left, right, self)
    }

    /// Attach the consumed range to the output.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let out = "a".test(item('a').with_range());
    /// assert_eq!(out.map(|(c, _)| c), Some('a'));
    /// ```
    #[inline(always)]
    fn with_range(self) -> prim::WithRange<Self>
    where
        Self: Sized,
    {
        prim::with_range(self)
    }

    /// Attach the consumed span to the output.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let out = "a".test(item('a').with_span());
    /// assert_eq!(out.map(|(c, _)| c), Some('a'));
    /// ```
    #[inline(always)]
    fn with_span(self) -> prim::WithSpan<Self>
    where
        Self: Sized,
        I::Pos: ToSpan,
    {
        prim::with_span(self)
    }

    /// Attach the consumed sequence to the output.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let out = "ab".test(item('a').with_seq());
    /// assert_eq!(out.map(|(c, seq)| (c, seq)), Some(('a', "a")));
    /// ```
    #[inline(always)]
    fn with_seq(self) -> prim::WithSeq<Self>
    where
        Self: Sized,
        I: SeqInput,
    {
        prim::with_seq(self)
    }

    /// Combine two parsers as a choice.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').or(item('b'));
    /// let out = "b".test(parser);
    /// assert_eq!(out, Some('b'));
    /// ```
    #[inline(always)]
    fn or<P>(self, other: P) -> choice::Choice<(Self, P)>
    where
        Self: Sized,
        P: SkipParserOnce<I, N, L, E>,
    {
        choice::choice((self, other))
    }

    /// Replace the output with a constant value.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let out = "a".test(item('a').to(1));
    /// assert_eq!(out, Some(1));
    /// ```
    #[inline(always)]
    fn to<O>(self, value: O) -> then::To<Self, O>
    where
        Self: Sized,
    {
        then::to(self, value)
    }

    /// Discard the output and return `()`.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let out = "a".test(item('a').skip());
    /// assert_eq!(out, Some(()));
    /// ```
    #[inline(always)]
    fn skip(self) -> then::Skip<Self>
    where
        Self: Sized,
    {
        then::skip(self)
    }
}
pub trait SkipParserMut<
    I: Input,
    N: Reborrow = (),
    L: RbBack = (),
    E: ErrorSink<I::Pos> = LatestSink<<I as Input>::Pos, StdErr<<I as Input>::Item>>,
>: SkipParserOnce<I, N, L, E>
{
    /// Run a parser mutably and discard its output.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    /// use chasa::input::IsCut;
    /// use chasa::LatestSink;
    ///
    /// let mut input = "a";
    /// let mut errors = LatestSink::new();
    /// let mut is_cut = false;
    /// let mut parser = item('a');
    /// let out = parser.discard_mut(In::new(&mut input, &mut errors, IsCut::new(&mut is_cut)));
    /// assert_eq!(out, Some(()));
    /// ```
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()>;

    /// Parse zero or more items and discard output.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').many_skip();
    /// let out = "aa".test(parser);
    /// assert_eq!(out, Some(()));
    /// ```
    #[inline(always)]
    fn many_skip(self) -> many::SkipMany<Self>
    where
        Self: Sized,
    {
        many::many_skip(self)
    }

    /// Parse one or more items and discard output.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').many1_skip();
    /// let out = "b".test(parser);
    /// assert_eq!(out, None);
    /// ```
    #[inline(always)]
    fn many1_skip(self) -> many::SkipMany1<Self>
    where
        Self: Sized,
    {
        many::many1_skip(self)
    }

    fn by_mut(&mut self) -> prim::MutParser<'_, Self>
    where
        Self: Sized,
    {
        prim::MutParser(self)
    }
}
pub trait SkipParser<
    I: Input,
    N: Reborrow = (),
    L: RbBack = (),
    E: ErrorSink<I::Pos> = LatestSink<<I as Input>::Pos, StdErr<<I as Input>::Item>>,
>: SkipParserMut<I, N, L, E>
{
    /// Run a parser by reference and discard its output.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    /// use chasa::input::IsCut;
    /// use chasa::LatestSink;
    ///
    /// let mut input = "a";
    /// let mut errors = LatestSink::new();
    /// let mut is_cut = false;
    /// let parser = item('a');
    /// let out = parser.discard(In::new(&mut input, &mut errors, IsCut::new(&mut is_cut)));
    /// assert_eq!(out, Some(()));
    /// ```
    fn discard(&self, i: In<I, N, L, E>) -> Option<()>;

    fn by_ref(&self) -> prim::RefParser<'_, Self>
    where
        Self: Sized,
    {
        prim::RefParser(self)
    }
}

pub trait ParserOnce<
    I: Input,
    N: Reborrow = (),
    L: RbBack = (),
    E: ErrorSink<I::Pos> = LatestSink<<I as Input>::Pos, StdErr<<I as Input>::Item>>,
>: SkipParserOnce<I, N, L, E>
{
    type Out;
    fn parse_once(self, i: In<I, N, L, E>) -> Option<Self::Out>;

    /// Chain a parser with access to the input.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').then_once(|c, _| Some((c, 1)));
    /// let out = "a".test(parser);
    /// assert_eq!(out, Some(('a', 1)));
    /// ```
    #[inline(always)]
    fn then_once<F, O>(self, f: F) -> then::Then<Self, F>
    where
        Self: Sized,
        F: FnOnce(Self::Out, In<I, N, L, E>) -> Option<O>,
    {
        then::then_once(self, f)
    }

    /// Map a parser output with `FnOnce`.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').map_once(|c| c.to_ascii_uppercase());
    /// let out = "a".test(parser);
    /// assert_eq!(out, Some('A'));
    /// ```
    #[inline(always)]
    fn map_once<F, O>(self, f: F) -> then::Map<Self, F>
    where
        Self: Sized,
        F: FnOnce(Self::Out) -> O,
    {
        then::map(self, f)
    }

    /// Map a parser output with a fallible function.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').and_then_once(|c| if c == 'a' { Some(1) } else { None });
    /// let out = "a".test(parser);
    /// assert_eq!(out, Some(1));
    /// ```
    #[inline(always)]
    fn and_then_once<F, O>(self, f: F) -> then::AndThen<Self, F>
    where
        Self: Sized,
        F: FnOnce(Self::Out) -> Option<O>,
    {
        then::and_then_once(self, f)
    }

    /// Bind the output to another parser.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').bind_once(|_| value(1));
    /// let out = "a".test(parser);
    /// assert_eq!(out, Some(1));
    /// ```
    #[inline(always)]
    fn bind_once<F, P>(self, f: F) -> then::Bind<Self, F>
    where
        Self: Sized,
        F: FnOnce(Self::Out) -> P,
        P: ParserOnce<I, N, L, E>,
    {
        then::bind(self, f)
    }
}
pub trait ParserMut<
    I: Input,
    N: Reborrow = (),
    L: RbBack = (),
    E: ErrorSink<I::Pos> = LatestSink<<I as Input>::Pos, StdErr<<I as Input>::Item>>,
>: ParserOnce<I, N, L, E> + SkipParserMut<I, N, L, E>
{
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<Self::Out>;

    /// Chain a parser with mutable access to the input.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let mut count = 0;
    /// let parser = item('a').then_mut(|c, _| {
    ///     count += 1;
    ///     Some((c, count))
    /// });
    /// let out = "a".test(parser);
    /// assert_eq!(out, Some(('a', 1)));
    /// ```
    #[inline(always)]
    fn then_mut<F, O>(self, f: F) -> then::Then<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Out, In<I, N, L, E>) -> Option<O>,
    {
        then::then_mut(self, f)
    }

    /// Map a parser output with `FnMut`.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let mut count = 0;
    /// let parser = item('a').map_mut(|_| {
    ///     count += 1;
    ///     count
    /// });
    /// let out = "a".test(parser);
    /// assert_eq!(out, Some(1));
    /// ```
    #[inline(always)]
    fn map_mut<F, O>(self, f: F) -> then::Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Out) -> O,
    {
        then::map(self, f)
    }

    /// Map a parser output with a fallible `FnMut`.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let mut seen = false;
    /// let parser = item('a').and_then_mut(|c| {
    ///     seen = true;
    ///     if c == 'a' { Some(1) } else { None }
    /// });
    /// let out = "a".test(parser);
    /// assert_eq!(out, Some(1));
    /// assert!(seen);
    /// ```
    #[inline(always)]
    fn and_then_mut<F, O>(self, f: F) -> then::AndThen<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Out) -> Option<O>,
    {
        then::and_then_mut(self, f)
    }

    /// Bind the output to another parser with `FnMut`.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let mut count = 0;
    /// let parser = item('a').bind_mut(|_| {
    ///     count += 1;
    ///     value(count)
    /// });
    /// let out = "a".test(parser);
    /// assert_eq!(out, Some(1));
    /// ```
    #[inline(always)]
    fn bind_mut<F, P>(self, f: F) -> then::Bind<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Out) -> P,
        P: ParserOnce<I, N, L, E>,
    {
        then::bind(self, f)
    }

    /// Parse zero or more items.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let out: Option<String> = "aa".test(item('a').many());
    /// assert_eq!(out, Some("aa".to_string()));
    /// ```
    #[inline(always)]
    fn many<O>(self) -> many::Many<Self, O>
    where
        Self: Sized,
        O: FromIterator<Self::Out>,
    {
        many::many(self)
    }

    /// Parse one or more items.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let out: Option<String> = "aa".test(item('a').many1());
    /// assert_eq!(out, Some("aa".to_string()));
    /// ```
    #[inline(always)]
    fn many1<O>(self) -> many::Many1<Self, O>
    where
        Self: Sized,
        O: FromIterator<Self::Out>,
    {
        many::many1(self)
    }

    /// Parse zero or more items and map the iterator.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').many_map_once(|it| it.count());
    /// let out = "aa".test(parser);
    /// assert_eq!(out, Some(2));
    /// ```
    #[inline(always)]
    fn many_map_once<O, F>(self, f: F) -> many::ManyMap<Self, F>
    where
        Self: Sized,
        F: FnOnce(many::ManyMapIterator<Self, I, N, L, E, Self::Out>) -> O,
    {
        many::many_map_once(self, f)
    }

    /// Parse zero or more items and map with `FnMut`.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let mut seen = 0;
    /// let parser = item('a').many_map_mut(|it| {
    ///     seen += it.count();
    ///     seen
    /// });
    /// let out = "aa".test(parser);
    /// assert_eq!(out, Some(2));
    /// ```
    #[inline(always)]
    fn many_map_mut<O, F>(self, f: F) -> many::ManyMap<Self, F>
    where
        Self: Sized,
        F: FnMut(many::ManyMapIterator<Self, I, N, L, E, Self::Out>) -> O,
    {
        many::many_map_mut(self, f)
    }

    /// Loop a parser with a mutable step function.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    /// use std::ops::ControlFlow;
    ///
    /// let parser = any.flow_mut(0usize, |n, c| {
    ///     if c == 'b' {
    ///         ControlFlow::Break(n)
    ///     } else {
    ///         ControlFlow::Continue(n + 1)
    ///     }
    /// });
    /// let out = "aab".test(parser);
    /// assert_eq!(out, Some(2));
    /// ```
    #[inline(always)]
    fn flow_mut<C, S, Step>(self, state: S, step: Step) -> flow::Flow<Self, S, Step>
    where
        Self: Sized,
        Step: FnMut(S, Self::Out) -> ControlFlow<C, S>,
    {
        flow::Flow::new(self, state, step)
    }

    /// Parse `ControlFlow` items and collect continuations.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    /// use std::ops::ControlFlow;
    ///
    /// let take = choice((
    ///     map(item(']'), ControlFlow::Break),
    ///     map(any, ControlFlow::Continue),
    /// ));
    /// let out: Option<(String, Option<char>)> = "ab]".test(take.flow_many());
    /// assert_eq!(out, Some(("ab".to_string(), Some(']'))));
    /// ```
    #[inline(always)]
    fn flow_many<O, C, B>(self) -> flow::FlowMany<Self, O>
    where
        Self: Sized + ParserMut<I, N, L, E, Out = ControlFlow<B, C>>,
        O: FromIterator<C>,
    {
        flow::FlowMany::new(self)
    }

    /// Parse zero or more items until `till` succeeds, returning both.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let out: Option<(String, char)> = "ab]".test(any.many_till(item(']')));
    /// assert_eq!(out, Some(("ab".to_string(), ']')));
    /// ```
    #[inline(always)]
    fn many_till<Q, O>(self, till: Q) -> flow::ManyTill<Self, Q, O>
    where
        Self: Sized + ParserMut<I, N, L, E>,
        Q: ParserMut<I, N, L, E>,
        O: FromIterator<Self::Out>,
    {
        flow::many_till(self, till)
    }

    /// Parse `ControlFlow` items and map the iterator.
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
    /// let parser = take.flow_many_map_once(
    ///     |it: FlowManyIterator<'_, '_, _, _, _, _, _, _, _>| it.count(),
    /// );
    /// let out = "ab]".test(parser);
    /// assert_eq!(out, Some((2, Some(']'))));
    /// ```
    #[inline(always)]
    fn flow_many_map_once<F, O, C, B>(self, f: F) -> flow::FlowManyMap<Self, F>
    where
        Self: Sized + ParserMut<I, N, L, E, Out = ControlFlow<B, C>>,
        F: for<'a, 'b> FnOnce(flow::FlowManyIterator<'a, 'b, Self, I, N, L, E, C, B>) -> O,
    {
        flow::flow_many_map_once(self, f)
    }

    /// Parse `ControlFlow` items and map with `FnMut`.
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
    /// let mut seen = 0;
    /// let parser = take.flow_many_map_mut(
    ///     |it: FlowManyIterator<'_, '_, _, _, _, _, _, _, _>| {
    ///         seen += it.count();
    ///         seen
    ///     },
    /// );
    /// let out = "ab]".test(parser);
    /// assert_eq!(out, Some((2, Some(']'))));
    /// ```
    #[inline(always)]
    fn flow_many_map_mut<F, O, C, B>(self, f: F) -> flow::FlowManyMap<Self, F>
    where
        Self: Sized + ParserMut<I, N, L, E, Out = ControlFlow<B, C>>,
        F: for<'a, 'b> FnMut(flow::FlowManyIterator<'a, 'b, Self, I, N, L, E, C, B>) -> O,
    {
        flow::flow_many_map_mut(self, f)
    }

    /// Parse a separated list.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let out: Option<String> = "a,a".test(item('a').sep(item(',').map(|_| ())));
    /// assert_eq!(out, Some("aa".to_string()));
    /// ```
    #[inline(always)]
    fn sep<O, Q>(self, sep_p: Q) -> sep::Sep<O, sep::iter::Zero, sep::iter::Allow, Self, Q>
    where
        Self: Sized,
        Q: SkipParserMut<I, N, L, E>,
        O: FromIterator<Self::Out>,
    {
        sep::sep(self, sep_p)
    }

    /// Parse a non-empty separated list.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let out: Option<String> = "a,a".test(item('a').sep1(item(',').map(|_| ())));
    /// assert_eq!(out, Some("aa".to_string()));
    /// ```
    #[inline(always)]
    fn sep1<O, Q>(self, sep_p: Q) -> sep::Sep<O, sep::iter::One, sep::iter::Allow, Self, Q>
    where
        Self: Sized,
        Q: SkipParserMut<I, N, L, E>,
        O: FromIterator<Self::Out>,
    {
        sep::sep1(self, sep_p)
    }

    /// Parse a separated list and map the iterator.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').sep_map_once(item(',').map(|_| ()), |it| it.count());
    /// let out = "a,a".test(parser);
    /// assert_eq!(out, Some(2));
    /// ```
    #[inline(always)]
    fn sep_map_once<Q, F, O>(
        self,
        sep_p: Q,
        f: F,
    ) -> sep::SepMap<sep::iter::Zero, sep::iter::Allow, Self, Q, F>
    where
        Self: Sized,
        Q: SkipParserMut<I, N, L, E>,
        F: FnOnce(
            sep::SepMapIterator<Self, Q, I, N, L, E, Self::Out, sep::iter::Zero, sep::iter::Allow>,
        ) -> O,
    {
        sep::sep_map_once(self, sep_p, f)
    }

    /// Parse a separated list and map with `FnMut`.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let mut seen = 0;
    /// let parser = item('a').sep_map_mut(item(',').map(|_| ()), |it| {
    ///     seen += it.count();
    ///     seen
    /// });
    /// let out = "a,a".test(parser);
    /// assert_eq!(out, Some(2));
    /// ```
    #[inline(always)]
    fn sep_map_mut<Q, F, O>(
        self,
        sep_p: Q,
        f: F,
    ) -> sep::SepMap<sep::iter::Zero, sep::iter::Allow, Self, Q, F>
    where
        Self: Sized,
        Q: SkipParserMut<I, N, L, E>,
        F: FnMut(
            sep::SepMapIterator<Self, Q, I, N, L, E, Self::Out, sep::iter::Zero, sep::iter::Allow>,
        ) -> O,
    {
        sep::sep_map_mut(self, sep_p, f)
    }

    /// Reduce a separated list with a binary operator.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let term = item('1').map(|_| 1usize);
    /// let op = item('+').map(|_| ());
    /// let parser = term.sep_reduce(op, |acc, _, rhs| acc + rhs);
    /// let out = "1+1+1".test(parser);
    /// assert_eq!(out, Some(3));
    /// ```
    #[inline(always)]
    fn sep_reduce<Q, F, Op>(self, op: Q, f: F) -> sep::SepReduce<Self, Q, F>
    where
        Self: Sized,
        Q: ParserMut<I, N, L, E, Out = Op>,
    {
        sep::sep_reduce(self, op, f)
    }
}
pub trait Parser<
    I: Input,
    N: Reborrow = (),
    L: RbBack = (),
    E: ErrorSink<I::Pos> = LatestSink<<I as Input>::Pos, StdErr<<I as Input>::Item>>,
>: ParserMut<I, N, L, E> + SkipParser<I, N, L, E>
{
    fn parse(&self, i: In<I, N, L, E>) -> Option<Self::Out>;

    /// Chain a parser with access to the input.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').then(|c, _| Some(c));
    /// let out = "a".test(parser);
    /// assert_eq!(out, Some('a'));
    /// ```
    #[inline(always)]
    fn then<F, O>(self, f: F) -> then::Then<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Out, In<I, N, L, E>) -> Option<O>,
    {
        then::then(self, f)
    }

    /// Map a parser output with `Fn`.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').map(|c| c.to_ascii_uppercase());
    /// let out = "a".test(parser);
    /// assert_eq!(out, Some('A'));
    /// ```
    #[inline(always)]
    fn map<F, O>(self, f: F) -> then::Map<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Out) -> O,
    {
        then::map(self, f)
    }

    /// Map a parser output with a fallible `Fn`.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').and_then(|c| if c == 'a' { Some(1) } else { None });
    /// let out = "a".test(parser);
    /// assert_eq!(out, Some(1));
    /// ```
    #[inline(always)]
    fn and_then<F, O>(self, f: F) -> then::AndThen<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Out) -> Option<O>,
    {
        then::and_then(self, f)
    }

    /// Bind the output to another parser.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').bind(|_| value(1));
    /// let out = "a".test(parser);
    /// assert_eq!(out, Some(1));
    /// ```
    #[inline(always)]
    fn bind<F, P>(self, f: F) -> then::Bind<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Out) -> P,
        P: ParserOnce<I, N, L, E>,
    {
        then::bind(self, f)
    }

    /// Parse zero or more items and map the iterator.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').many_map(|it| it.count());
    /// let out = "aa".test(parser);
    /// assert_eq!(out, Some(2));
    /// ```
    #[inline(always)]
    fn many_map<O, F>(self, f: F) -> many::ManyMap<Self, F>
    where
        Self: Sized,
        F: Fn(many::ManyMapIterator<Self, I, N, L, E, Self::Out>) -> O,
    {
        many::many_map(self, f)
    }

    /// Loop a parser with a step function.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    /// use std::ops::ControlFlow;
    ///
    /// let parser = any.flow(0usize, |n, c| {
    ///     if c == 'b' {
    ///         ControlFlow::Break(n)
    ///     } else {
    ///         ControlFlow::Continue(n + 1)
    ///     }
    /// });
    /// let out = "aab".test(parser);
    /// assert_eq!(out, Some(2));
    /// ```
    #[inline(always)]
    fn flow<C, S, Step>(self, state: S, step: Step) -> flow::Flow<Self, S, Step>
    where
        Self: Sized,
        Step: Fn(S, Self::Out) -> ControlFlow<C, S>,
    {
        flow::Flow::new(self, state, step)
    }

    /// Parse `ControlFlow` items and map the iterator.
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
    /// let parser = take.flow_many_map(
    ///     |it: FlowManyIterator<'_, '_, _, _, _, _, _, _, _>| it.count(),
    /// );
    /// let out = "ab]".test(parser);
    /// assert_eq!(out, Some((2, Some(']'))));
    /// ```
    #[inline(always)]
    fn flow_many_map<F, O, C, B>(self, f: F) -> flow::FlowManyMap<Self, F>
    where
        Self: Sized + Parser<I, N, L, E, Out = ControlFlow<B, C>>,
        F: for<'a, 'b> Fn(flow::FlowManyIterator<'a, 'b, Self, I, N, L, E, C, B>) -> O,
    {
        flow::flow_many_map(self, f)
    }

    /// Parse a separated list and map the iterator.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').sep_map(item(',').map(|_| ()), |it| it.count());
    /// let out = "a,a".test(parser);
    /// assert_eq!(out, Some(2));
    /// ```
    #[inline(always)]
    fn sep_map<Q, F, O>(
        self,
        sep_p: Q,
        f: F,
    ) -> sep::SepMap<sep::iter::Zero, sep::iter::Allow, Self, Q, F>
    where
        Self: Sized,
        Q: SkipParser<I, N, L, E>,
        F: Fn(
            sep::SepMapIterator<Self, Q, I, N, L, E, Self::Out, sep::iter::Zero, sep::iter::Allow>,
        ) -> O,
    {
        sep::sep_map(self, sep_p, f)
    }

    /// Parse a non-empty separated list and map the iterator.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let parser = item('a').sep1_map(item(',').map(|_| ()), |it| it.count());
    /// let out = "a,a".test(parser);
    /// assert_eq!(out, Some(2));
    /// ```
    #[inline(always)]
    fn sep1_map<Q, F, O>(
        self,
        sep_p: Q,
        f: F,
    ) -> sep::SepMap<sep::iter::One, sep::iter::Allow, Self, Q, F>
    where
        Self: Sized,
        Q: SkipParser<I, N, L, E>,
        F: Fn(
            sep::SepMapIterator<Self, Q, I, N, L, E, Self::Out, sep::iter::One, sep::iter::Allow>,
        ) -> O,
    {
        sep::sep1_map(self, sep_p, f)
    }
}

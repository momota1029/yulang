mod counter;
mod impls;
mod is_cut;
mod offset;
mod with_counter;

use std::borrow::Cow;
use std::ops::{ControlFlow, Range};

use reborrow_generic::{Reborrow, Reborrowed};

pub use counter::Counter;
pub use is_cut::IsCut;
pub use offset::Offset;
pub use with_counter::WithCounter;

use crate::back::{Back, RbBack};
use crate::error::std::{Expected, StdErr, Unexpected, UnexpectedEndOfInput, UnexpectedItem};
use crate::error::{ErrorSink, LatestSink};
use crate::parser::sep::iter::Trailing as _;
use crate::parser::{ParserMut, ParserOnce, SkipParserMut, SkipParserOnce};

pub trait Input: Back {
    type Pos: Ord + Clone;
    type Item: Clone;

    fn index(&self) -> u64;
    fn pos(&self) -> Self::Pos;
    fn next(&mut self) -> Option<Self::Item>;
    fn commit(&mut self);

    fn with_counter<C: Counter<Self::Item>>(self, counter: C) -> WithCounter<Self, C>
    where
        Self: Sized,
    {
        WithCounter {
            input: self,
            counter,
        }
    }

    fn with_len(self) -> WithCounter<Self, usize>
    where
        Self: Sized,
    {
        self.with_counter(0)
    }

    /// Run a parser and return its output.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let mut input = "ab";
    /// let out = input.test(item('a'));
    /// assert_eq!(out, Some('a'));
    /// ```
    fn test<P>(&mut self, parser: P) -> Option<P::Out>
    where
        Self: Sized,
        P: ParserOnce<Self>,
    {
        let mut errors = LatestSink::new();
        let mut is_cut = false;
        parser.parse_once(In::new(self, &mut errors, IsCut::new(&mut is_cut)))
    }

    /// Run a parser and return output with accumulated errors.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let mut input = "b";
    /// let (out, mut errors) = input.test_with_errors(item('a'));
    /// assert_eq!(out, None);
    /// assert!(errors.take_merged().is_some());
    /// ```
    fn test_with_errors<P>(
        &mut self,
        parser: P,
    ) -> (Option<P::Out>, LatestSink<Self::Pos, StdErr<Self::Item>>)
    where
        Self: Sized,
        P: ParserOnce<Self>,
    {
        let mut errors = LatestSink::new();
        let mut is_cut = false;
        let out = parser.parse_once(In::new(self, &mut errors, IsCut::new(&mut is_cut)));
        (out, errors)
    }
}

pub trait SeqInput: Input {
    type Seq;
    fn seq(start: Self::Checkpoint, end: Self::Checkpoint) -> Self::Seq;
}

pub trait ToSpan: Sized {
    type Span: Clone;
    fn span_to(&self, end: &Self) -> Self::Span;
}

impl ToSpan for usize {
    type Span = usize;
    fn span_to(&self, end: &Self) -> Self::Span {
        end.saturating_sub(*self)
    }
}

impl ToSpan for u64 {
    type Span = u64;
    fn span_to(&self, end: &Self) -> Self::Span {
        end.saturating_sub(*self)
    }
}

pub struct InputCheckpoint<I: Input, L: RbBack> {
    pub input: I::Checkpoint,
    pub local: L::Checkpoint,
}

impl<I: Input, L: RbBack> Clone for InputCheckpoint<I, L> {
    fn clone(&self) -> Self {
        Self {
            input: self.input.clone(),
            local: self.local.clone(),
        }
    }
}

#[derive(Reborrow)]
pub struct In<
    'a,
    I: Input,
    N: Reborrow + 'a = (),
    L: RbBack + 'a = (),
    E: ErrorSink<I::Pos> + 'a = LatestSink<<I as Input>::Pos, StdErr<<I as Input>::Item>>,
> {
    pub input: &'a mut I,
    pub env: N::Target<'a>,
    pub local: L::Target<'a>,
    pub errors: E::Target<'a>,
    pub(crate) is_cut: IsCut<'a>,
}

impl<'a, I: Input> In<'a, I, (), (), LatestSink<I::Pos, StdErr<<I as Input>::Item>>> {
    pub fn new(
        input: &'a mut I,
        errors: &'a mut LatestSink<I::Pos, StdErr<<I as Input>::Item>>,
        is_cut: IsCut<'a>,
    ) -> Self {
        Self {
            input,
            env: (),
            local: (),
            errors,
            is_cut,
        }
    }
}

impl<'a, I: Input, N: Reborrow + 'a, L: RbBack + 'a, E: ErrorSink<I::Pos> + 'a> Back
    for In<'a, I, N, L, E>
{
    type Checkpoint = InputCheckpoint<I, L>;

    fn checkpoint(&mut self) -> Self::Checkpoint {
        InputCheckpoint {
            input: self.input.checkpoint(),
            local: L::checkpoint(L::shorten_mut(&mut self.local)),
        }
    }

    fn rollback(&mut self, checkpoint: Self::Checkpoint) {
        self.input.rollback(checkpoint.input);
        L::rollback(L::shorten_mut(&mut self.local), checkpoint.local);
    }
}

impl<'a, I: Input, N: Reborrow, L: RbBack, E: ErrorSink<I::Pos>> In<'a, I, N, L, E> {
    pub fn capture_cut<O>(&mut self, f: impl FnOnce(In<I, N, L, E>) -> O) -> (O, bool) {
        self.is_cut.capture_cut(|is_cut| {
            f(In {
                input: &mut self.input,
                env: N::shorten_mut(&mut self.env),
                local: L::shorten_mut(&mut self.local),
                errors: E::shorten_mut(&mut self.errors),
                is_cut,
            })
        })
    }

    pub fn set_env<'b, N2: Reborrowed<'b>>(self, env: N2) -> In<'b, I, N2, L, E>
    where
        'a: 'b,
    {
        In {
            input: self.input,
            env,
            local: L::shorten(self.local),
            errors: E::shorten(self.errors),
            is_cut: IsCut::shorten(self.is_cut),
        }
    }

    pub fn get_env(self) -> (In<'a, I, (), L, E>, N::Target<'a>) {
        (
            In {
                input: self.input,
                env: (),
                local: self.local,
                errors: self.errors,
                is_cut: self.is_cut,
            },
            self.env,
        )
    }

    pub fn update_env<'b, N2: Reborrowed<'b>>(
        self,
        f: impl FnOnce(N::Target<'a>) -> N2,
    ) -> In<'b, I, N2, L, E>
    where
        'a: 'b,
    {
        In {
            input: self.input,
            env: f(self.env),
            local: L::shorten(self.local),
            errors: E::shorten(self.errors),
            is_cut: IsCut::shorten(self.is_cut),
        }
    }

    pub fn set_local<'b, L2: Reborrowed<'b> + RbBack>(self, local: L2) -> In<'b, I, N, L2, E>
    where
        'a: 'b,
    {
        In {
            input: self.input,
            env: N::shorten(self.env),
            local,
            errors: E::shorten(self.errors),
            is_cut: IsCut::shorten(self.is_cut),
        }
    }

    pub fn get_local(self) -> (In<'a, I, N, (), E>, L::Target<'a>) {
        (
            In {
                input: self.input,
                env: N::shorten(self.env),
                local: (),
                errors: self.errors,
                is_cut: self.is_cut,
            },
            self.local,
        )
    }

    #[inline(always)]
    pub fn pos(&self) -> I::Pos {
        self.input.pos()
    }

    #[inline(always)]
    pub fn index(&self) -> u64 {
        self.input.index()
    }

    #[inline(always)]
    pub fn commit(&mut self) {
        self.input.commit();
    }

    #[inline(always)]
    pub fn errors_checkpoint(&mut self) -> E::Checkpoint {
        E::checkpoint(E::shorten_mut(&mut self.errors))
    }

    #[inline(always)]
    pub fn errors_rollback(&mut self, checkpoint: E::Checkpoint) {
        E::rollback(E::shorten_mut(&mut self.errors), checkpoint);
    }

    #[inline(always)]
    pub fn cut(&mut self) {
        self.is_cut.cut();
        if self.is_cut.is_root {
            self.input.commit();
        }
    }

    #[inline]
    pub fn cut_after<P, O>(&mut self, parser: P) -> Option<O>
    where
        P: ParserOnce<I, N, L, E, Out = O>,
    {
        let out = parser.parse_once(self.rb())?;
        self.cut();
        Some(out)
    }

    #[inline]
    pub fn run<P, O>(&mut self, parser: P) -> Option<O>
    where
        P: ParserOnce<I, N, L, E, Out = O>,
    {
        parser.parse_once(self.rb())
    }

    #[inline]
    pub fn map<P, O, T, F>(&mut self, parser: P, f: F) -> Option<O>
    where
        P: ParserOnce<I, N, L, E, Out = T>,
        F: FnOnce(T) -> O,
    {
        self.run(parser).map(f)
    }

    #[inline]
    pub fn skip<P, O>(&mut self, parser: P) -> Option<()>
    where
        P: ParserOnce<I, N, L, E, Out = O>,
    {
        self.run(parser).map(|_| ())
    }

    #[inline]
    pub fn when(&mut self, value: bool) -> Option<()> {
        if value { Some(()) } else { None }
    }

    #[inline]
    pub fn choice<Ps>(&mut self, parsers: Ps) -> Option<Ps::Out>
    where
        Ps: crate::parser::choice::ChoiceParserOnce<I, N, L, E>,
    {
        parsers.parse_once_choice(self.rb())
    }

    #[inline]
    pub fn seq<P, Q, O, T>(&mut self, left: P, right: Q) -> Option<(O, T)>
    where
        P: ParserOnce<I, N, L, E, Out = O>,
        Q: ParserOnce<I, N, L, E, Out = T>,
    {
        let left = left.parse_once(self.rb())?;
        let right = right.parse_once(self.rb())?;
        Some((left, right))
    }

    #[inline]
    pub fn left<P, Q, O, T>(&mut self, left: P, right: Q) -> Option<O>
    where
        P: ParserOnce<I, N, L, E, Out = O>,
        Q: ParserOnce<I, N, L, E, Out = T>,
    {
        let out = left.parse_once(self.rb())?;
        right.parse_once(self.rb())?;
        Some(out)
    }

    #[inline]
    pub fn right<P, Q, O, T>(&mut self, left: P, right: Q) -> Option<T>
    where
        P: ParserOnce<I, N, L, E, Out = O>,
        Q: ParserOnce<I, N, L, E, Out = T>,
    {
        left.parse_once(self.rb())?;
        right.parse_once(self.rb())
    }

    #[inline]
    pub fn bind<P, F, Q, O, T>(&mut self, parser: P, f: F) -> Option<O>
    where
        P: ParserOnce<I, N, L, E, Out = T>,
        F: FnOnce(T) -> Q,
        Q: ParserOnce<I, N, L, E, Out = O>,
    {
        let out = parser.parse_once(self.rb())?;
        f(out).parse_once(self.rb())
    }

    #[inline]
    pub fn between<P, Q, R, O, T, U>(&mut self, left: P, mid: Q, right: R) -> Option<T>
    where
        P: ParserOnce<I, N, L, E, Out = O>,
        Q: ParserOnce<I, N, L, E, Out = T>,
        R: ParserOnce<I, N, L, E, Out = U>,
    {
        left.parse_once(self.rb())?;
        let out = mid.parse_once(self.rb())?;
        right.parse_once(self.rb())?;
        Some(out)
    }

    #[inline]
    pub fn to<P, O, T>(&mut self, parser: P, value: O) -> Option<O>
    where
        P: ParserOnce<I, N, L, E, Out = T>,
    {
        parser.parse_once(self.rb())?;
        Some(value)
    }

    #[inline]
    pub fn lookahead<P, O>(&mut self, parser: P) -> Option<O>
    where
        P: ParserOnce<I, N, L, E, Out = O>,
    {
        let checkpoint = self.checkpoint();
        let errors_checkpoint = self.errors_checkpoint();
        let (out, is_cut) = self.capture_cut(|i| parser.parse_once(i));
        if out.is_some() {
            self.errors_rollback(errors_checkpoint);
        }
        if out.is_some() || !is_cut {
            self.rollback(checkpoint);
        }
        out
    }

    #[inline]
    pub fn not<P>(&mut self, parser: P) -> Option<()>
    where
        P: SkipParserOnce<I, N, L, E>,
    {
        let checkpoint = self.checkpoint();
        let errors_checkpoint = self.errors_checkpoint();
        match self.capture_cut(|i| parser.discard_once(i)) {
            (Some(_), true) => None,
            (Some(_), false) => {
                self.rollback(checkpoint);
                None
            }
            (None, true) => None,
            (None, false) => {
                self.errors_rollback(errors_checkpoint);
                self.rollback(checkpoint);
                Some(())
            }
        }
    }

    #[inline]
    pub fn maybe<P, O>(&mut self, parser: P) -> Option<Option<O>>
    where
        P: ParserOnce<I, N, L, E, Out = O>,
    {
        let checkpoint = self.checkpoint();
        let errors_checkpoint = self.errors_checkpoint();
        match self.capture_cut(|i| parser.parse_once(i)) {
            (Some(value), _) => Some(Some(value)),
            (None, true) => None,
            (None, false) => {
                self.errors_rollback(errors_checkpoint);
                self.rollback(checkpoint);
                Some(None)
            }
        }
    }

    #[inline]
    pub fn maybe_fn<O>(
        &mut self,
        f: impl FnOnce(In<I, N, L, E>) -> Option<O>,
    ) -> Option<Option<O>> {
        self.maybe(crate::prelude::from_fn_once(f))
    }

    #[inline]
    pub fn label<P, S, O>(&mut self, parser: P, label: S) -> Option<O>
    where
        P: ParserOnce<I, N, L, E, Out = O>,
        S: Into<Cow<'static, str>>,
        Expected<()>: Into<E::Error>,
    {
        self.label_with(parser, || label)
    }

    #[inline]
    pub fn label_with<P, F, S, O>(&mut self, parser: P, f: F) -> Option<O>
    where
        P: ParserOnce<I, N, L, E, Out = O>,
        F: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        Expected<()>: Into<E::Error>,
    {
        let index = self.input.index();
        let out = parser.parse_once(self.rb());
        if out.is_some() {
            return out;
        }
        let expected = Expected::new(index, f(), ());
        let pos = self.pos();
        E::push(
            E::shorten_mut(&mut self.errors),
            pos.clone()..pos,
            expected.into(),
        );
        None
    }

    #[inline]
    pub fn with_range<P, O>(&mut self, parser: P) -> Option<(O, Range<I::Pos>)>
    where
        P: ParserOnce<I, N, L, E, Out = O>,
    {
        let p0 = self.pos();
        let out = parser.parse_once(self.rb())?;
        let p1 = self.pos();
        Some((out, p0..p1))
    }

    #[inline]
    pub fn with_span<P, O>(&mut self, parser: P) -> Option<(O, <I::Pos as ToSpan>::Span)>
    where
        I::Pos: ToSpan,
        P: ParserOnce<I, N, L, E, Out = O>,
    {
        let (out, range) = self.with_range(parser)?;
        let span = range.start.span_to(&range.end);
        Some((out, span))
    }

    #[inline]
    pub fn with_seq<O>(
        &mut self,
        parser: impl ParserOnce<I, N, L, E, Out = O>,
    ) -> Option<(O, I::Seq)>
    where
        I: SeqInput,
    {
        let start = self.input.checkpoint();
        let res = self.run(parser)?;
        let end = self.input.checkpoint();
        Some((res, I::seq(start, end)))
    }

    #[inline]
    pub fn any(&mut self) -> Option<I::Item>
    where
        UnexpectedEndOfInput: Into<E::Error>,
    {
        crate::parser::item::any(self.rb())
    }

    #[inline]
    pub fn eoi(&mut self) -> Option<()>
    where
        UnexpectedItem<I::Item>: Into<E::Error>,
    {
        crate::parser::item::eoi(self.rb())
    }

    #[inline]
    pub fn item<T>(&mut self, item: T) -> Option<I::Item>
    where
        T: PartialEq<I::Item>,
        I::Item: Clone,
        Unexpected<I::Item>: Into<E::Error>,
    {
        crate::parser::item::run_satisfy(self.rb(), |value| item == value.clone())
    }

    #[inline]
    pub fn satisfy<F>(&mut self, f: F) -> Option<I::Item>
    where
        F: FnOnce(I::Item) -> bool,
        I::Item: Clone,
        Unexpected<I::Item>: Into<E::Error>,
    {
        crate::parser::item::run_satisfy(self.rb(), |item| f(item.clone()))
    }

    #[inline]
    pub fn one_of<S>(&mut self, items: S) -> Option<I::Item>
    where
        S: crate::parser::item::set::ItemSet<I::Item>,
        Unexpected<I::Item>: Into<E::Error>,
    {
        crate::parser::item::run_satisfy(self.rb(), |item| items.has(item))
    }

    #[inline]
    pub fn none_of<S>(&mut self, items: S) -> Option<I::Item>
    where
        S: crate::parser::item::set::ItemSet<I::Item>,
        Unexpected<I::Item>: Into<E::Error>,
    {
        crate::parser::item::run_satisfy(self.rb(), |item| !items.has(item))
    }

    #[inline]
    pub fn tag(&mut self, tag: &'static str) -> Option<()>
    where
        I: Input<Item = char>,
        Unexpected<I::Item>: Into<E::Error>,
    {
        for expected in tag.chars() {
            let p0 = self.input.pos();
            match self.input.next() {
                Some(actual) if actual == expected => {}
                Some(actual) => {
                    let p1 = self.input.pos();
                    E::push(
                        E::shorten_mut(&mut self.errors),
                        p0..p1,
                        Unexpected::Item(actual).into(),
                    );
                    return None;
                }
                None => {
                    let p1 = self.input.pos();
                    E::push(
                        E::shorten_mut(&mut self.errors),
                        p0..p1,
                        Unexpected::EndOfInput.into(),
                    );
                    return None;
                }
            }
        }
        Some(())
    }

    #[inline]
    pub fn satisfy_map<F, O>(&mut self, f: F) -> Option<O>
    where
        F: FnOnce(I::Item) -> Option<O>,
        I::Item: Clone,
        Unexpected<I::Item>: Into<E::Error>,
    {
        crate::parser::item::run_satisfy_map(self.rb(), f)
    }

    #[inline]
    pub fn many<P, O>(&mut self, parser: P) -> Option<O>
    where
        P: ParserMut<I, N, L, E>,
        O: FromIterator<P::Out>,
    {
        let mut hard_failure = false;
        let it = crate::parser::many::ManyIterator {
            parser,
            i: self.rb(),
            is_end: false,
            hard_failure: &mut hard_failure,
            _marker: core::marker::PhantomData,
        };
        let out: O = it.collect();
        if hard_failure { None } else { Some(out) }
    }

    #[inline]
    pub fn many1<P, O>(&mut self, parser: P) -> Option<O>
    where
        P: ParserMut<I, N, L, E>,
        O: FromIterator<P::Out>,
    {
        let mut parser = parser;
        let mut input = self.rb();
        let first = match input.maybe(parser.by_mut()) {
            Some(Some(value)) => value,
            Some(None) => return None,
            None => return None,
        };
        let mut hard_failure = false;
        let it = crate::parser::many::ManyIterator {
            parser,
            i: input.rb(),
            is_end: false,
            hard_failure: &mut hard_failure,
            _marker: core::marker::PhantomData,
        };
        let out: O = core::iter::once(first).chain(it).collect();
        if hard_failure { None } else { Some(out) }
    }

    #[inline]
    pub fn many_skip<P>(&mut self, parser: P) -> Option<()>
    where
        P: SkipParserMut<I, N, L, E>,
    {
        let mut parser = parser;
        let mut input = self.rb();
        loop {
            let checkpoint = input.checkpoint();
            let errors_checkpoint = input.errors_checkpoint();
            match input.capture_cut(|i| parser.discard_mut(i)) {
                (Some(_), _) => {}
                (None, true) => return None,
                (None, false) => {
                    input.errors_rollback(errors_checkpoint);
                    input.rollback(checkpoint);
                    break;
                }
            }
        }
        Some(())
    }

    #[inline]
    pub fn many1_skip<P>(&mut self, parser: P) -> Option<()>
    where
        P: SkipParserMut<I, N, L, E>,
    {
        let mut parser = parser;
        let mut input = self.rb();
        let checkpoint = input.checkpoint();
        let errors_checkpoint = input.errors_checkpoint();
        match input.capture_cut(|i| parser.discard_mut(i)) {
            (Some(_), _) => {}
            (None, true) => return None,
            (None, false) => {
                input.errors_rollback(errors_checkpoint);
                input.rollback(checkpoint);
                return None;
            }
        }
        loop {
            let checkpoint = input.checkpoint();
            let errors_checkpoint = input.errors_checkpoint();
            match input.capture_cut(|i| parser.discard_mut(i)) {
                (Some(_), _) => {}
                (None, true) => return None,
                (None, false) => {
                    input.errors_rollback(errors_checkpoint);
                    input.rollback(checkpoint);
                    break;
                }
            }
        }
        Some(())
    }

    #[inline]
    pub fn many_map<P, F, O>(&mut self, parser: P, f: F) -> Option<O>
    where
        P: ParserMut<I, N, L, E>,
        F: FnOnce(crate::parser::many::ManyMapIterator<P, I, N, L, E, P::Out>) -> O,
    {
        let mut hard_failure = false;
        let mut parser = parser;
        let it = crate::parser::many::ManyIterator {
            parser: crate::parser::prim::RefOrMutParser::new_mut(&mut parser),
            i: self.rb(),
            is_end: false,
            hard_failure: &mut hard_failure,
            _marker: core::marker::PhantomData,
        };
        let out = f(it);
        if hard_failure { None } else { Some(out) }
    }

    #[inline]
    pub fn sep<P, Q, O>(&mut self, item: P, sep: Q) -> Option<O>
    where
        P: ParserMut<I, N, L, E>,
        Q: SkipParserMut<I, N, L, E>,
        O: FromIterator<P::Out>,
    {
        let mut hard_failure = false;
        let mut did_trail = false;
        let iter = crate::parser::sep::SepIterator {
            is_first: true,
            item,
            sep,
            input: self.rb(),
            is_end: false,
            did_trail: &mut did_trail,
            hard_failure: &mut hard_failure,
            _mode: core::marker::PhantomData::<
                fn() -> (
                    crate::parser::sep::iter::Zero,
                    crate::parser::sep::iter::Allow,
                ),
            >,
            _marker: core::marker::PhantomData,
        };
        let out: O = iter.collect();
        if hard_failure || !crate::parser::sep::iter::Allow::validate_end(did_trail) {
            None
        } else {
            Some(out)
        }
    }

    #[inline]
    pub fn sep1<P, Q, O>(&mut self, item: P, sep: Q) -> Option<O>
    where
        P: ParserMut<I, N, L, E>,
        Q: SkipParserMut<I, N, L, E>,
        O: FromIterator<P::Out>,
    {
        let mut hard_failure = false;
        let mut did_trail = false;
        let iter = crate::parser::sep::SepIterator {
            is_first: true,
            item,
            sep,
            input: self.rb(),
            is_end: false,
            did_trail: &mut did_trail,
            hard_failure: &mut hard_failure,
            _mode: core::marker::PhantomData::<
                fn() -> (
                    crate::parser::sep::iter::One,
                    crate::parser::sep::iter::Allow,
                ),
            >,
            _marker: core::marker::PhantomData,
        };
        let out: O = iter.collect();
        if hard_failure || !crate::parser::sep::iter::Allow::validate_end(did_trail) {
            None
        } else {
            Some(out)
        }
    }

    #[inline]
    pub fn sep_use_trail<P, Q, O>(&mut self, item: P, sep: Q) -> Option<(O, bool)>
    where
        P: ParserMut<I, N, L, E>,
        Q: SkipParserMut<I, N, L, E>,
        O: FromIterator<P::Out>,
    {
        let mut hard_failure = false;
        let mut did_trail = false;
        let iter = crate::parser::sep::SepIterator {
            is_first: true,
            item,
            sep,
            input: self.rb(),
            is_end: false,
            did_trail: &mut did_trail,
            hard_failure: &mut hard_failure,
            _mode: core::marker::PhantomData::<
                fn() -> (
                    crate::parser::sep::iter::Zero,
                    crate::parser::sep::iter::Allow,
                ),
            >,
            _marker: core::marker::PhantomData,
        };
        let out: O = iter.collect();
        if hard_failure || !crate::parser::sep::iter::Allow::validate_end(did_trail) {
            None
        } else {
            Some((out, did_trail))
        }
    }

    #[inline]
    pub fn sep_map<P, Q, F, O>(&mut self, item: P, sep: Q, f: F) -> Option<O>
    where
        P: ParserMut<I, N, L, E>,
        Q: SkipParserMut<I, N, L, E>,
        F: FnOnce(
            crate::parser::sep::SepIterator<
                P,
                Q,
                I,
                N,
                L,
                E,
                P::Out,
                crate::parser::sep::iter::Zero,
                crate::parser::sep::iter::Allow,
            >,
        ) -> O,
    {
        crate::parser::sep::sep_map_run(item, sep, f, self.rb())
    }

    #[inline]
    pub fn sep1_map<P, Q, F, O>(&mut self, item: P, sep: Q, f: F) -> Option<O>
    where
        P: ParserMut<I, N, L, E>,
        Q: SkipParserMut<I, N, L, E>,
        F: FnOnce(
            crate::parser::sep::SepIterator<
                P,
                Q,
                I,
                N,
                L,
                E,
                P::Out,
                crate::parser::sep::iter::One,
                crate::parser::sep::iter::Allow,
            >,
        ) -> O,
    {
        crate::parser::sep::sep_map_run(item, sep, f, self.rb())
    }

    #[inline]
    pub fn sep_reduce<P, Q, F>(&mut self, term: P, op: Q, f: F) -> Option<P::Out>
    where
        P: ParserMut<I, N, L, E>,
        Q: ParserMut<I, N, L, E>,
        F: FnMut(P::Out, Q::Out, P::Out) -> P::Out,
    {
        let mut term = term;
        let mut op = op;
        let mut f = f;
        let mut left = term.parse_mut(self.rb())?;
        loop {
            let checkpoint = self.checkpoint();
            let errors_checkpoint = self.errors_checkpoint();
            match self.capture_cut(|i| op.parse_mut(i)) {
                (Some(op_value), _) => {
                    let right = term.parse_mut(self.rb())?;
                    left = f(left, op_value, right);
                }
                (None, true) => return None,
                (None, false) => {
                    self.errors_rollback(errors_checkpoint);
                    self.rollback(checkpoint);
                    return Some(left);
                }
            }
        }
    }

    #[inline]
    pub fn flow<T, P, F, O>(&mut self, init: T, parser: P, f: F) -> Option<O>
    where
        P: ParserMut<I, N, L, E>,
        F: FnMut(T, P::Out) -> ControlFlow<O, T>,
    {
        let mut parser = parser;
        let mut state = init;
        let mut step = f;
        loop {
            let value = parser.parse_mut(self.rb())?;
            match step(state, value) {
                ControlFlow::Continue(next) => state = next,
                ControlFlow::Break(out) => return Some(out),
            }
        }
    }

    #[inline]
    pub fn flow_many<P, C, B, O>(&mut self, parser: P) -> Option<(O, Option<B>)>
    where
        P: ParserMut<I, N, L, E, Out = ControlFlow<B, C>>,
        O: FromIterator<C>,
    {
        let mut hard_failure = false;
        let mut break_ = None;
        let it = crate::parser::flow::RawFlowManyIterator {
            parser,
            input: self.rb(),
            done: false,
            break_: &mut break_,
            hard_failure: &mut hard_failure,
            _phantom: core::marker::PhantomData,
        };
        let out: O = it.collect();
        if hard_failure {
            None
        } else {
            Some((out, break_))
        }
    }

    #[inline]
    pub fn many_till<P, Q, C, B, O>(&mut self, parser: P, till: Q) -> Option<(O, B)>
    where
        P: ParserMut<I, N, L, E, Out = C>,
        Q: ParserMut<I, N, L, E, Out = B>,
        O: FromIterator<C>,
    {
        let mut hard_failure = false;
        let mut break_ = None;
        let it = crate::parser::flow::RawManyTillIterator {
            parser,
            till,
            input: self.rb(),
            done: false,
            break_: &mut break_,
            hard_failure: &mut hard_failure,
            _phantom: core::marker::PhantomData,
        };
        let out: O = it.collect();
        if hard_failure {
            None
        } else {
            Some((out, break_?))
        }
    }

    #[inline]
    pub fn flow_many_map<P, F, O, C, B>(&mut self, parser: P, f: F) -> Option<(O, Option<B>)>
    where
        P: ParserMut<I, N, L, E, Out = ControlFlow<B, C>>,
        F: for<'s, 'p> FnOnce(
            crate::parser::flow::FlowManyIterator<'s, 'p, P, I, N, L, E, C, B>,
        ) -> O,
    {
        let mut hard_failure = false;
        let mut break_ = None;
        let mut parser = parser;
        let it = crate::parser::flow::RawFlowManyIterator {
            parser: crate::parser::prim::RefOrMutParser::new_mut(&mut parser),
            input: self.rb(),
            done: false,
            break_: &mut break_,
            hard_failure: &mut hard_failure,
            _phantom: core::marker::PhantomData,
        };
        let out = f(it);
        if hard_failure {
            None
        } else {
            Some((out, break_))
        }
    }
}

#[cfg(test)]
mod tests;

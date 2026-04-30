use reborrow_generic::Reborrow;
use seq_macro::seq;

use crate::back::{Back, RbBack};
use crate::error::ErrorSink;
use crate::input::{In, Input};
use crate::parser::{Parser, ParserMut, ParserOnce, SkipParser, SkipParserMut, SkipParserOnce};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Choice<Ps>(Ps);

/// Pick the first successful parser.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "b".test(or(item('a'), item('b')));
/// assert_eq!(out, Some('b'));
/// ```
#[inline(always)]
pub fn or<P, Q, I, N, L, E>(left: P, right: Q) -> Choice<(P, Q)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
    Q: SkipParserOnce<I, N, L, E>,
{
    choice((left, right))
}

/// Try each parser in order and return the first success.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "b".test(choice((item('a'), item('b'))));
/// assert_eq!(out, Some('b'));
///
/// let out = "c".test(choice((item('a'), item('b'))));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn choice<Ps, I, N, L, E>(parsers: Ps) -> Choice<Ps>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Ps: ChoiceSkipParserOnce<I, N, L, E>,
{
    Choice(parsers)
}

pub trait ChoiceSkipParserOnce<I: Input, N: Reborrow, L: RbBack, E: ErrorSink<I::Pos>> {
    fn discard_once_choice(self, input: In<I, N, L, E>) -> Option<()>;
}

pub trait ChoiceSkipParserMut<I: Input, N: Reborrow, L: RbBack, E: ErrorSink<I::Pos>>:
    ChoiceSkipParserOnce<I, N, L, E>
{
    fn discard_mut_choice(&mut self, input: In<I, N, L, E>) -> Option<()>;
}

pub trait ChoiceSkipParser<I: Input, N: Reborrow, L: RbBack, E: ErrorSink<I::Pos>>:
    ChoiceSkipParserMut<I, N, L, E>
{
    fn discard_choice(&self, input: In<I, N, L, E>) -> Option<()>;
}

pub trait ChoiceParserOnce<I: Input, N: Reborrow, L: RbBack, E: ErrorSink<I::Pos>> {
    type Out;
    fn parse_once_choice(self, input: In<I, N, L, E>) -> Option<Self::Out>;
}

pub trait ChoiceParserMut<I: Input, N: Reborrow, L: RbBack, E: ErrorSink<I::Pos>>:
    ChoiceParserOnce<I, N, L, E>
{
    fn parse_mut_choice(&mut self, input: In<I, N, L, E>) -> Option<Self::Out>;
}

pub trait ChoiceParser<I: Input, N: Reborrow, L: RbBack, E: ErrorSink<I::Pos>>:
    ChoiceParserMut<I, N, L, E>
{
    fn parse_choice(&self, input: In<I, N, L, E>) -> Option<Self::Out>;
}

impl<Ps, I, N, L, E> SkipParserOnce<I, N, L, E> for Choice<Ps>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Ps: ChoiceSkipParserOnce<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, input: In<I, N, L, E>) -> Option<()> {
        self.0.discard_once_choice(input)
    }
}

impl<Ps, I, N, L, E> SkipParserMut<I, N, L, E> for Choice<Ps>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Ps: ChoiceSkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, input: In<I, N, L, E>) -> Option<()> {
        self.0.discard_mut_choice(input)
    }
}

impl<Ps, I, N, L, E> SkipParser<I, N, L, E> for Choice<Ps>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Ps: ChoiceSkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, input: In<I, N, L, E>) -> Option<()> {
        self.0.discard_choice(input)
    }
}

impl<Ps, I, N, L, E> ParserOnce<I, N, L, E> for Choice<Ps>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Ps: ChoiceParserOnce<I, N, L, E> + ChoiceSkipParserOnce<I, N, L, E>,
{
    type Out = Ps::Out;
    #[inline]
    fn parse_once(self, input: In<I, N, L, E>) -> Option<Self::Out> {
        self.0.parse_once_choice(input)
    }
}

impl<Ps, I, N, L, E> ParserMut<I, N, L, E> for Choice<Ps>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Ps: ChoiceParserMut<I, N, L, E> + ChoiceSkipParserMut<I, N, L, E>,
{
    #[inline]
    fn parse_mut(&mut self, input: In<I, N, L, E>) -> Option<Self::Out> {
        self.0.parse_mut_choice(input)
    }
}

impl<Ps, I, N, L, E> Parser<I, N, L, E> for Choice<Ps>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Ps: ChoiceParser<I, N, L, E> + ChoiceSkipParser<I, N, L, E>,
{
    #[inline]
    fn parse(&self, input: In<I, N, L, E>) -> Option<Self::Out> {
        self.0.parse_choice(input)
    }
}

macro_rules! choice_fn2 {
    ($run:ident, $checkpoint:ident, $errors_checkpoint:ident, $input:ident, $p1:ident, $p2:ident, $($p3:ident,)+) => {{
        match $p1.$run($input.rb()) {
            Some(v) => {
                $input.errors_rollback($errors_checkpoint.clone());
                Some(v)
            }
            None if *$input.is_cut.is_cut => None,
            None => {
                $input.rollback($checkpoint.clone());
                choice_fn2!($run, $checkpoint, $errors_checkpoint, $input, $p2, $($p3,)+)
            }
        }
    }};
    ($run:ident, $checkpoint:ident, $errors_checkpoint:ident, $input:ident, $p1:ident, $p2:ident,) => {{
        match $p1.$run($input.rb()) {
            Some(v) => {
                $input.errors_rollback($errors_checkpoint.clone());
                Some(v)
            }
            None if *$input.is_cut.is_cut => None,
            None => {
                $input.rollback($checkpoint);
                match $p2.$run($input.rb()) {
                    Some(v) => {
                        $input.errors_rollback($errors_checkpoint);
                        Some(v)
                    }
                    None => None,
                }
            }
        }
    }};
    ($run:ident, $checkpoint:ident, $errors_checkpoint:ident, $input:ident, $p1:ident,) => {{
        match $p1.$run($input.rb()) {
            Some(v) => {
                $input.errors_rollback($errors_checkpoint);
                Some(v)
            }
            None => None,
        }
    }};
}

macro_rules! choice_impl {
    ($N:literal) => {
        seq!(n in 1..=$N {
            impl<#(P~n,)* I, N, L, E> ChoiceSkipParserOnce<I, N, L, E> for (#(P~n,)*)
            where
                I: Input,
                N: Reborrow,
                L: RbBack,
                E: ErrorSink<I::Pos>,
                #(P~n: SkipParserOnce<I, N, L, E>,)*
            {
                #[allow(unused_variables, unused_mut)]
                #[inline]
                fn discard_once_choice(self, mut i: In<I, N, L, E>) -> Option<()> {
                    let (#(p~n,)*) = self;
                    let checkpoint = i.checkpoint();
                    let errors_checkpoint = i.errors_checkpoint();
                    i.capture_cut(|mut i| {
                        choice_fn2!(discard_once, checkpoint, errors_checkpoint, i, #(p~n,)*)
                    }).0
                }
            }

            impl<#(P~n,)* I, N, L, E> ChoiceSkipParserMut<I, N, L, E> for (#(P~n,)*)
            where
                I: Input,
                N: Reborrow,
                L: RbBack,
                E: ErrorSink<I::Pos>,
                #(P~n: SkipParserMut<I, N, L, E>,)*
            {
                #[allow(unused_variables, unused_mut)]
                #[inline]
                fn discard_mut_choice(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
                    let (#(p~n,)*) = self;
                    let checkpoint = i.checkpoint();
                    let errors_checkpoint = i.errors_checkpoint();
                    i.capture_cut(|mut i| {
                        choice_fn2!(discard_mut, checkpoint, errors_checkpoint, i, #(p~n,)*)
                    }).0
                }
            }

            impl<#(P~n,)* I, N, L, E> ChoiceSkipParser<I, N, L, E> for (#(P~n,)*)
            where
                I: Input,
                N: Reborrow,
                L: RbBack,
                E: ErrorSink<I::Pos>,
                #(P~n: SkipParser<I, N, L, E>,)*
            {
                #[allow(unused_variables, unused_mut)]
                #[inline]
                fn discard_choice(&self, mut i: In<I, N, L, E>) -> Option<()> {
                    let (#(p~n,)*) = self;
                    let checkpoint = i.checkpoint();
                    let errors_checkpoint = i.errors_checkpoint();
                    i.capture_cut(|mut i| {
                        choice_fn2!(discard, checkpoint, errors_checkpoint, i, #(p~n,)*)
                    }).0
                }
            }

            impl<#(P~n,)* O, I, N, L, E> ChoiceParserOnce<I, N, L, E> for (#(P~n,)*)
            where
                I: Input,
                N: Reborrow,
                L: RbBack,
                E: ErrorSink<I::Pos>,
                #(P~n: ParserOnce<I, N, L, E, Out = O>,)*
            {
                type Out = O;
                #[allow(unused_variables, unused_mut)]
                #[inline]
                fn parse_once_choice(self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
                    let (#(p~n,)*) = self;
                    let checkpoint = i.checkpoint();
                    let errors_checkpoint = i.errors_checkpoint();
                    i.capture_cut(|mut i| {
                        choice_fn2!(parse_once, checkpoint, errors_checkpoint, i, #(p~n,)*)
                    }).0
                }
            }

            impl<#(P~n,)* O, I, N, L, E> ChoiceParserMut<I, N, L, E> for (#(P~n,)*)
            where
                I: Input,
                N: Reborrow,
                L: RbBack,
                E: ErrorSink<I::Pos>,
                #(P~n: ParserMut<I, N, L, E, Out = O>,)*
            {
                #[allow(unused_variables, unused_mut)]
                #[inline]
                fn parse_mut_choice(&mut self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
                    let (#(p~n,)*) = self;
                    let checkpoint = i.checkpoint();
                    let errors_checkpoint = i.errors_checkpoint();
                    i.capture_cut(|mut i| {
                        choice_fn2!(parse_mut, checkpoint, errors_checkpoint, i, #(p~n,)*)
                    }).0
                }
            }

            impl<#(P~n,)* O, I, N, L, E> ChoiceParser<I, N, L, E> for (#(P~n,)*)
            where
                I: Input,
                N: Reborrow,
                L: RbBack,
                E: ErrorSink<I::Pos>,
                #(P~n: Parser<I, N, L, E, Out = O>,)*
            {
                #[allow(unused_variables, unused_mut)]
                #[inline]
                fn parse_choice(&self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
                    let (#(p~n,)*) = self;
                    let checkpoint = i.checkpoint();
                    let errors_checkpoint = i.errors_checkpoint();
                    i.capture_cut(|mut i| {
                        choice_fn2!(parse, checkpoint, errors_checkpoint, i, #(p~n,)*)
                    }).0
                }
            }
        });
    };
}

seq!(N in 1..=32 { choice_impl!(N); });

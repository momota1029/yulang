use core::marker::PhantomData;

use reborrow_generic::Reborrow;
use seq_macro::seq;

use crate::back::RbBack;
use crate::error::ErrorSink;
use crate::error::std::Unexpected;
use crate::input::{In, Input};
use crate::parser::prim::{from_fn_once, value};
use crate::parser::{Parser, ParserMut, ParserOnce, SkipParser, SkipParserMut, SkipParserOnce};

pub trait TrieState: Sized {
    type Item;
    type Value;
    fn step(&mut self, ch: Self::Item) -> bool;
    fn value(&self) -> Option<Self::Value>;

    fn longest_match<A>(self) -> TrieParser<Self, A> {
        TrieParser(self, PhantomData)
    }

    fn longest_match_then<O, F, I, N, L, E>(self, f: F) -> TrieThen<Self, F, (I, N, L, E)>
    where
        I: Input,
        N: Reborrow,
        L: RbBack,
        E: ErrorSink<I::Pos>,
        F: FnMut(Self::Item, Self::Value, In<I, N, L, E>) -> Option<O>,
    {
        TrieThen(self, f, PhantomData)
    }
}

pub struct TrieParser<T, A>(T, PhantomData<fn() -> A>);

fn run_trie_parser<T, I, N, L, E>(state: &mut T, mut i: In<I, N, L, E>) -> Option<T::Value>
where
    T: TrieState<Item = I::Item>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    I::Item: Clone,
    Unexpected<I::Item>: Into<E::Error>,
{
    i.satisfy(|c| state.step(c))?;
    if let Some(v) = state.value() {
        i.choice((from_fn_once(|i| run_trie_parser(state, i)), value(v)))
    } else {
        run_trie_parser(state, i)
    }
}

impl<I, N, L, E, T> SkipParserOnce<I, N, L, E> for TrieParser<T, (I, N, L, E)>
where
    T: TrieState<Item = I::Item>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    I::Item: Clone,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        let mut state = self.0;
        run_trie_parser(&mut state, i).map(|_| ())
    }
}

impl<I, N, L, E, T> ParserOnce<I, N, L, E> for TrieParser<T, (I, N, L, E)>
where
    T: TrieState<Item = I::Item>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    I::Item: Clone,
    Unexpected<I::Item>: Into<E::Error>,
{
    type Out = T::Value;
    #[inline]
    fn parse_once(self, i: In<I, N, L, E>) -> Option<Self::Out> {
        let mut state = self.0;
        run_trie_parser(&mut state, i)
    }
}

impl<I, N, L, E, T> SkipParserMut<I, N, L, E> for TrieParser<T, (I, N, L, E)>
where
    T: TrieState<Item = I::Item>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    I::Item: Clone,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        run_trie_parser(&mut self.0, i).map(|_| ())
    }
}

impl<I, N, L, E, T> ParserMut<I, N, L, E> for TrieParser<T, (I, N, L, E)>
where
    T: TrieState<Item = I::Item>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    I::Item: Clone,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_trie_parser(&mut self.0, i)
    }
}

impl<I, N, L, E, T> SkipParser<I, N, L, E> for TrieParser<T, (I, N, L, E)>
where
    T: TrieState<Item = I::Item> + Clone,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    I::Item: Clone,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        let mut state = self.0.clone();
        run_trie_parser(&mut state, i).map(|_| ())
    }
}

impl<I, N, L, E, T> Parser<I, N, L, E> for TrieParser<T, (I, N, L, E)>
where
    T: TrieState<Item = I::Item> + Clone,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    I::Item: Clone,
    Unexpected<I::Item>: Into<E::Error>,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<Self::Out> {
        let mut state = self.0.clone();
        run_trie_parser(&mut state, i)
    }
}

pub struct TrieThen<T, F, A>(T, F, PhantomData<fn() -> A>);

fn run_trie_then<T, O, I, N, L, E>(
    state: &mut T,
    f: &mut impl FnMut(T::Item, T::Value, In<I, N, L, E>) -> Option<O>,
    mut i: In<I, N, L, E>,
) -> Option<O>
where
    T: TrieState<Item = I::Item>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    I::Item: Clone,
    Unexpected<I::Item>: Into<E::Error>,
{
    let c = i.satisfy(|c| state.step(c))?;
    if let Some(v) = state.value() {
        if let Some(o) = i.maybe(from_fn_once(|i| run_trie_then(state, f, i)))? {
            Some(o)
        } else {
            f(c, v, i)
        }
    } else {
        run_trie_then(state, f, i)
    }
}

impl<T, F, O, I, N, L, E> SkipParserOnce<I, N, L, E> for TrieThen<T, F, (I, N, L, E)>
where
    T: TrieState<Item = I::Item>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    I::Item: Clone,
    Unexpected<I::Item>: Into<E::Error>,
    F: FnMut(T::Item, T::Value, In<I, N, L, E>) -> Option<O>,
{
    #[inline]
    fn discard_once(mut self, i: In<I, N, L, E>) -> Option<()> {
        run_trie_then(&mut self.0, &mut self.1, i).map(|_| ())
    }
}

impl<T, F, O, I, N, L, E> ParserOnce<I, N, L, E> for TrieThen<T, F, (I, N, L, E)>
where
    T: TrieState<Item = I::Item>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    I::Item: Clone,
    Unexpected<I::Item>: Into<E::Error>,
    F: FnMut(T::Item, T::Value, In<I, N, L, E>) -> Option<O>,
{
    type Out = O;
    #[inline]
    fn parse_once(mut self, i: In<I, N, L, E>) -> Option<O> {
        run_trie_then(&mut self.0, &mut self.1, i)
    }
}

impl<T, F, O, I, N, L, E> SkipParserMut<I, N, L, E> for TrieThen<T, F, (I, N, L, E)>
where
    T: TrieState<Item = I::Item>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    I::Item: Clone,
    Unexpected<I::Item>: Into<E::Error>,
    F: FnMut(T::Item, T::Value, In<I, N, L, E>) -> Option<O>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        run_trie_then(&mut self.0, &mut self.1, i).map(|_| ())
    }
}

impl<T, F, O, I, N, L, E> ParserMut<I, N, L, E> for TrieThen<T, F, (I, N, L, E)>
where
    T: TrieState<Item = I::Item>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    I::Item: Clone,
    Unexpected<I::Item>: Into<E::Error>,
    F: FnMut(T::Item, T::Value, In<I, N, L, E>) -> Option<O>,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<Self::Out> {
        run_trie_then(&mut self.0, &mut self.1, i)
    }
}

impl<T, F, O, I, N, L, E> SkipParser<I, N, L, E> for TrieThen<T, F, (I, N, L, E)>
where
    T: TrieState<Item = I::Item> + Clone,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    I::Item: Clone,
    Unexpected<I::Item>: Into<E::Error>,
    F: FnMut(T::Item, T::Value, In<I, N, L, E>) -> Option<O> + Clone,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        let mut state = self.0.clone();
        let mut f = self.1.clone();
        run_trie_then(&mut state, &mut f, i).map(|_| ())
    }
}

impl<T, F, O, I, N, L, E> Parser<I, N, L, E> for TrieThen<T, F, (I, N, L, E)>
where
    T: TrieState<Item = I::Item> + Clone,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    I::Item: Clone,
    Unexpected<I::Item>: Into<E::Error>,
    F: FnMut(T::Item, T::Value, In<I, N, L, E>) -> Option<O> + Clone,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<Self::Out> {
        let mut state = self.0.clone();
        let mut f = self.1.clone();
        run_trie_then(&mut state, &mut f, i)
    }
}

macro_rules! trie_state_impl {
    ($N:literal) => {
        seq!(n in 1..=$N {
            impl<Item, Value, #(T~n,)*> TrieState for ( #(T~n,)* )
            where
                Item: Clone,
                #(T~n: TrieState<Item = Item, Value = Value>,)*
            {
                type Item = Item;
                type Value = Value;

                fn step(&mut self, ch: Self::Item) -> bool {
                    let ( #(s~n,)* ) = self;
                    let mut any = false;
                    #( any |= s~n.step(ch.clone()); )*
                    any
                }

                fn value(&self) -> Option<Self::Value> {
                    let ( #(s~n,)* ) = self;
                    #( let v~n = s~n.value(); if v~n.is_some() { return v~n; } )*
                    None
                }
            }
        });
    };
}

seq!(N in 2..=16 { trie_state_impl!(N); });

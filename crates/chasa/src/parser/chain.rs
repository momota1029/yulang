/// Tuple parsers: `(p1, p2, ...)` run in sequence and return a tuple of outputs.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ab".test((item('a'), item('b')));
/// assert_eq!(out, Some(('a', 'b')));
/// ```
use reborrow_generic::Reborrow;
use seq_macro::seq;

use crate::back::{Back, RbBack};
use crate::error::ErrorSink;
use crate::input::{In, Input};
use crate::parser::{Parser, ParserMut, ParserOnce, SkipParser, SkipParserMut, SkipParserOnce};

macro_rules! chain_impl {
    ($N:literal) => {
        seq!(n in 1..=$N {
            impl<#(P~n,)* I, N, L, E> SkipParserOnce<I, N, L, E> for (#(P~n,)*)
            where
                I: Input,
                N: Reborrow,
                L: RbBack,
                E: ErrorSink<I::Pos>,
                #(P~n: SkipParserOnce<I, N, L, E>, )*
            {
                fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
                    let (#(p~n,)*) = self;
                    let checkpoint = i.checkpoint();
                    let (out, cut) = i.capture_cut(|mut i| {
                        #(p~n.discard_once(i.rb())?;)*
                        Some(())
                    });
                    if out.is_some() || cut {
                        return out;
                    }
                    i.rollback(checkpoint);
                    None
                }
            }

            impl<#(P~n,)* I, N, L, E> SkipParserMut<I, N, L, E> for (#(P~n,)*)
            where
                I: Input,
                N: Reborrow,
                L: RbBack,
                E: ErrorSink<I::Pos>,
                #(P~n: SkipParserMut<I, N, L, E>, )*
            {
                fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
                    let (#(p~n,)*) = self;
                    let checkpoint = i.checkpoint();
                    let (out, cut) = i.capture_cut(|mut i| {
                        #(p~n.discard_mut(i.rb())?;)*
                        Some(())
                    });
                    if out.is_some() || cut {
                        return out;
                    }
                    i.rollback(checkpoint);
                    None
                }
            }

            impl<#(P~n,)* I, N, L, E> SkipParser<I, N, L, E> for (#(P~n,)*)
            where
                I: Input,
                N: Reborrow,
                L: RbBack,
                E: ErrorSink<I::Pos>,
                #(P~n: SkipParser<I, N, L, E>, )*
            {
                fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
                    let (#(p~n,)*) = self;
                    let checkpoint = i.checkpoint();
                    let (out, cut) = i.capture_cut(|mut i| {
                        #(p~n.discard(i.rb())?;)*
                        Some(())
                    });
                    if out.is_some() || cut {
                        return out;
                    }
                    i.rollback(checkpoint);
                    None
                }
            }

            impl<#(P~n, O~n,)* I, N, L, E> ParserOnce<I, N, L, E> for (#(P~n,)*)
            where
                I: Input,
                N: Reborrow,
                L: RbBack,
                E: ErrorSink<I::Pos>,
                #(P~n: ParserOnce<I, N, L, E, Out = O~n>, )*
            {
                type Out = (#(O~n,)*);
                #[allow(unused_variables, unused_mut)]
                fn parse_once(self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
                    let (#(p~n,)*) = self;
                    let checkpoint = i.checkpoint();
                    let (out, cut) = i.capture_cut(|mut i| {
                        Some((#(p~n.parse_once(i.rb())?,)*))
                    });
                    if out.is_some() || cut {
                        return out;
                    }
                    i.rollback(checkpoint);
                    None
                }
            }

            impl<#(P~n, O~n,)* I, N, L, E> ParserMut<I, N, L, E> for (#(P~n,)*)
            where
                I: Input,
                N: Reborrow,
                L: RbBack,
                E: ErrorSink<I::Pos>,
                #(P~n: ParserMut<I, N, L, E, Out = O~n>, )*
            {
                #[allow(unused_variables, unused_mut)]
                fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
                    let (#(p~n,)*) = self;
                    let checkpoint = i.checkpoint();
                    let (out, cut) = i.capture_cut(|mut i| {
                        Some((#(p~n.parse_mut(i.rb())?,)*))
                    });
                    if out.is_some() || cut {
                        return out;
                    }
                    i.rollback(checkpoint);
                    None
                }
            }

            impl<#(P~n, O~n,)* I, N, L, E> Parser<I, N, L, E> for (#(P~n,)*)
            where
                I: Input,
                N: Reborrow,
                L: RbBack,
                E: ErrorSink<I::Pos>,
                #(P~n: Parser<I, N, L, E, Out = O~n>, )*
            {
                #[allow(unused_variables, unused_mut)]
                fn parse(&self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
                    let (#(p~n,)*) = self;
                    let checkpoint = i.checkpoint();
                    let (out, cut) = i.capture_cut(|mut i| {
                        Some((#(p~n.parse(i.rb())?,)*))
                    });
                    if out.is_some() || cut {
                        return out;
                    }
                    i.rollback(checkpoint);
                    None
                }
            }
        });
    };
}

seq!(N in 1..=32 { chain_impl!(N); });

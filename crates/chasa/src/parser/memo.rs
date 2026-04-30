/// Memoization helpers for parser results.
use core::marker::PhantomData;

use reborrow_generic::Reborrow;

use crate::{
    back::{Back, Front, RbFront},
    error::ErrorSink,
    input::{In, Input, InputCheckpoint},
    parser::{Parser, ParserMut, ParserOnce, SkipParser, SkipParserMut, SkipParserOnce},
};

pub enum Coarse<H, B> {
    Hit(H),
    Back(B),
}

pub trait Memo<I: Input, L: RbFront, E: ErrorSink<I::Pos>> {
    type Out;
    fn memo(&mut self, pos: I::Pos, i: In<I, (), L, E>, out: Option<Self::Out>);
    fn restore(&mut self, i: In<I, (), L, E>) -> Option<Option<Self::Out>>;
    fn memo_restore(
        &mut self,
        pos: I::Pos,
        mut i: In<I, (), L, E>,
        out: Option<Self::Out>,
    ) -> Option<Self::Out> {
        self.memo(pos, i.rb(), out);
        self.restore(i).unwrap()
    }
}

/// A single-slot memo cell storing a position and optional output.
pub struct MemoCell<I: Input, L: RbFront, Out>(
    Option<(I::Pos, InputCheckpoint<I, L>, Option<Out>)>,
);
impl<I: Input, L: RbFront, Out> MemoCell<I, L, Out> {
    pub fn new() -> Self {
        Self(None)
    }
}
impl<I: Input, L: RbFront, Out> Default for MemoCell<I, L, Out> {
    fn default() -> Self {
        Self::new()
    }
}
impl<I: Input, L: RbFront, E: ErrorSink<I::Pos>, Out> Memo<I, L, E> for MemoCell<I, L, Out> {
    type Out = Out;
    fn memo(&mut self, pos: I::Pos, mut i: In<I, (), L, E>, out: Option<Self::Out>) {
        self.0 = Some((pos, i.checkpoint(), out));
    }
    fn restore(&mut self, mut i: In<I, (), L, E>) -> Option<Option<Self::Out>> {
        let pos = &self.0.as_ref()?.0;
        if pos == &i.pos() {
            let (_, checkpoint, out) = self.0.take().unwrap();
            i.rollback(checkpoint);
            return Some(out);
        }
        None
    }
    fn memo_restore(
        &mut self,
        _pos: I::Pos,
        _i: In<I, (), L, E>,
        out: Option<Self::Out>,
    ) -> Option<Self::Out> {
        out
    }
}

// 一番手軽なメモ化パーサ。`&self`はジェネリクス対応や値に使うかも知れないので一応。
/// Accessor trait for memoized parsers.
pub trait MemoAccessor<I: Input + Front, N: Reborrow, L: RbFront, E: ErrorSink<I::Pos>> {
    type Out;
    type Memo: Memo<I, L, E, Out = Self::Out>;
    fn access<'a>(env: N::Target<'a>) -> &'a mut Self::Memo;
    fn parse(&self, i: In<I, N, L, E>) -> Option<Self::Out>;

    fn memoize(&self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        let opt_o = {
            let (mut i, env) = i.rb().get_env();
            Self::access(env).restore(i.rb())
        };
        match opt_o {
            Some(o) => o,
            None => {
                let pos = i.pos();
                let o = self.parse(i.rb());
                let (mut i, env) = i.rb().get_env();
                Self::access(env).memo_restore(pos, i.rb(), o)
            }
        }
    }
    fn coarse<F: FnOnce(Self::Out) -> Coarse<O, Self::Out>, O>(
        &self,
        mut i: In<I, N, L, E>,
        f: F,
    ) -> Option<O> {
        let pos = i.pos();
        match f(self.memoize(i.rb())?) {
            Coarse::Hit(o) => Some(o),
            Coarse::Back(back) => {
                let (mut i, env) = i.rb().get_env();
                Self::access(env).memo(pos, i.rb(), Some(back));
                None
            }
        }
    }

    fn weak(&self, mut i: In<I, N, L, E>) -> Option<Self::Out> {
        let (mut i_inner, env) = i.rb().get_env();
        Self::access(env).restore(i_inner.rb()).flatten()
    }

    fn weak_coarse<F: FnOnce(Self::Out) -> Coarse<O, Self::Out>, O>(
        &self,
        mut i: In<I, N, L, E>,
        f: F,
    ) -> Option<O> {
        let token = self.weak(i.rb())?;

        match f(token) {
            Coarse::Hit(o) => Some(o),
            Coarse::Back(back) => {
                let pos = i.pos();
                let (mut i_inner, env) = i.rb().get_env();
                Self::access(env).memo(pos, i_inner.rb(), Some(back));
                None
            }
        }
    }

    fn coarse_p_once<'a, F, O, A>(&'a self, f: F) -> CoarseParser<'a, Self, F, A>
    where
        Self: Sized,
        F: FnOnce(Self::Out) -> Coarse<O, Self::Out>,
    {
        CoarseParser(self, f, PhantomData)
    }
    fn coarse_p_mut<'a, F, O, A>(&'a self, f: F) -> CoarseParser<'a, Self, F, A>
    where
        Self: Sized,
        F: FnMut(Self::Out) -> Coarse<O, Self::Out>,
    {
        CoarseParser(self, f, PhantomData)
    }
    fn coarse_p<'a, F, O, A>(&'a self, f: F) -> CoarseParser<'a, Self, F, A>
    where
        Self: Sized,
        F: Fn(Self::Out) -> Coarse<O, Self::Out>,
    {
        CoarseParser(self, f, PhantomData)
    }
}

pub struct CoarseParser<'a, M, F, A>(&'a M, F, PhantomData<fn() -> A>);
impl<
    'a,
    M: MemoAccessor<I, N, L, E>,
    F: FnOnce(M::Out) -> Coarse<O, M::Out>,
    O,
    I: Input + Front,
    N: Reborrow,
    L: RbFront,
    E: ErrorSink<I::Pos>,
> ParserOnce<I, N, L, E> for CoarseParser<'a, M, F, (O, I, N, L, E)>
{
    type Out = O;
    fn parse_once(self, i: In<I, N, L, E>) -> Option<Self::Out> {
        self.0.coarse(i, self.1)
    }
}

impl<
    'a,
    M: MemoAccessor<I, N, L, E>,
    F: FnOnce(M::Out) -> Coarse<O, M::Out>,
    O,
    I: Input + Front,
    N: Reborrow,
    L: RbFront,
    E: ErrorSink<I::Pos>,
> SkipParserOnce<I, N, L, E> for CoarseParser<'a, M, F, (O, I, N, L, E)>
{
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_once(i).map(|_| ())
    }
}

impl<
    'a,
    M: MemoAccessor<I, N, L, E>,
    F: FnMut(M::Out) -> Coarse<O, M::Out>,
    O,
    I: Input + Front,
    N: Reborrow,
    L: RbFront,
    E: ErrorSink<I::Pos>,
> SkipParserMut<I, N, L, E> for CoarseParser<'a, M, F, (O, I, N, L, E)>
{
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.0.coarse(i, |out| (self.1)(out)).map(|_| ())
    }
}

impl<
    'a,
    M: MemoAccessor<I, N, L, E>,
    F: Fn(M::Out) -> Coarse<O, M::Out>,
    O,
    I: Input + Front,
    N: Reborrow,
    L: RbFront,
    E: ErrorSink<I::Pos>,
> SkipParser<I, N, L, E> for CoarseParser<'a, M, F, (O, I, N, L, E)>
{
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.0.coarse(i, |out| (self.1)(out)).map(|_| ())
    }
}

impl<
    'a,
    M: MemoAccessor<I, N, L, E>,
    F: FnMut(M::Out) -> Coarse<O, M::Out>,
    O,
    I: Input + Front,
    N: Reborrow,
    L: RbFront,
    E: ErrorSink<I::Pos>,
> ParserMut<I, N, L, E> for CoarseParser<'a, M, F, (O, I, N, L, E)>
{
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<O> {
        self.0.coarse(i, |out| (self.1)(out))
    }
}

impl<
    'a,
    M: MemoAccessor<I, N, L, E>,
    F: Fn(M::Out) -> Coarse<O, M::Out>,
    O,
    I: Input + Front,
    N: Reborrow,
    L: RbFront,
    E: ErrorSink<I::Pos>,
> Parser<I, N, L, E> for CoarseParser<'a, M, F, (O, I, N, L, E)>
{
    fn parse(&self, i: In<I, N, L, E>) -> Option<O> {
        self.0.coarse(i, |out| (self.1)(out))
    }
}

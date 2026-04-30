use reborrow_generic::Reborrow;

use crate::back::RbBack;
use crate::error::ErrorSink;
use crate::input::{In, Input};
use crate::parser::{ParserMut, SkipParserMut, SkipParserOnce};

pub trait Count {
    fn first<I, N, L, E, P, O>(input: &mut In<I, N, L, E>, item: &mut P) -> Result<Option<O>, ()>
    where
        I: Input,
        N: Reborrow,
        L: RbBack,
        E: ErrorSink<I::Pos>,
        P: ParserMut<I, N, L, E, Out = O>;
}

#[derive(Debug, Clone, Copy, Hash, Default)]
pub struct Zero;
impl Count for Zero {
    #[inline]
    fn first<I, N, L, E, P, O>(input: &mut In<I, N, L, E>, item: &mut P) -> Result<Option<O>, ()>
    where
        I: Input,
        N: Reborrow,
        L: RbBack,
        E: ErrorSink<I::Pos>,
        P: ParserMut<I, N, L, E, Out = O>,
    {
        match input.maybe(item.by_mut()) {
            Some(Some(value)) => Ok(Some(value)),
            Some(None) => Ok(None),
            None => Err(()),
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, Default)]
pub struct One;
impl Count for One {
    #[inline]
    fn first<I, N, L, E, P, O>(input: &mut In<I, N, L, E>, item: &mut P) -> Result<Option<O>, ()>
    where
        I: Input,
        N: Reborrow,
        L: RbBack,
        E: ErrorSink<I::Pos>,
        P: ParserMut<I, N, L, E, Out = O>,
    {
        match item.parse_mut(input.rb()) {
            Some(value) => Ok(Some(value)),
            None => Err(()),
        }
    }
}

pub trait Trailing {
    fn validate_end(did_trail: bool) -> bool;

    fn second<I, N, L, E, P, Q, O>(
        input: &mut In<I, N, L, E>,
        sep: &mut Q,
        item: &mut P,
        did_trail: &mut bool,
    ) -> Result<Option<O>, ()>
    where
        I: Input,
        N: Reborrow,
        L: RbBack,
        E: ErrorSink<I::Pos>,
        P: ParserMut<I, N, L, E, Out = O>,
        Q: SkipParserMut<I, N, L, E>;
}

#[derive(Debug, Clone, Copy, Hash, Default)]
pub struct Allow;
impl Trailing for Allow {
    #[inline]
    fn validate_end(_: bool) -> bool {
        true
    }

    #[inline]
    fn second<I, N, L, E, P, Q, O>(
        input: &mut In<I, N, L, E>,
        sep: &mut Q,
        item: &mut P,
        did_trail: &mut bool,
    ) -> Result<Option<O>, ()>
    where
        I: Input,
        N: Reborrow,
        L: RbBack,
        E: ErrorSink<I::Pos>,
        P: ParserMut<I, N, L, E, Out = O>,
        Q: SkipParserMut<I, N, L, E>,
    {
        match input.maybe(sep.by_mut().skip()) {
            Some(Some(_)) => match input.maybe(item.by_mut()) {
                Some(Some(value)) => Ok(Some(value)),
                Some(None) => {
                    *did_trail = true;
                    Ok(None)
                }
                None => Err(()),
            },
            Some(None) => Ok(None),
            None => Err(()),
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, Default)]
pub struct No;
impl Trailing for No {
    #[inline]
    fn validate_end(_: bool) -> bool {
        true
    }

    #[inline]
    fn second<I, N, L, E, P, Q, O>(
        input: &mut In<I, N, L, E>,
        sep: &mut Q,
        item: &mut P,
        _did_trail: &mut bool,
    ) -> Result<Option<O>, ()>
    where
        I: Input,
        N: Reborrow,
        L: RbBack,
        E: ErrorSink<I::Pos>,
        P: ParserMut<I, N, L, E, Out = O>,
        Q: SkipParserMut<I, N, L, E>,
    {
        match input.maybe(sep.by_mut().skip()) {
            Some(Some(_)) => match item.parse_mut(input.rb()) {
                Some(value) => Ok(Some(value)),
                None => Err(()),
            },
            Some(None) => Ok(None),
            None => Err(()),
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, Default)]
pub struct Must;
impl Trailing for Must {
    #[inline]
    fn validate_end(did_trail: bool) -> bool {
        did_trail
    }

    #[inline]
    fn second<I, N, L, E, P, Q, O>(
        input: &mut In<I, N, L, E>,
        sep: &mut Q,
        item: &mut P,
        did_trail: &mut bool,
    ) -> Result<Option<O>, ()>
    where
        I: Input,
        N: Reborrow,
        L: RbBack,
        E: ErrorSink<I::Pos>,
        P: ParserMut<I, N, L, E, Out = O>,
        Q: SkipParserMut<I, N, L, E>,
    {
        match input.maybe(sep.by_mut().skip()) {
            Some(Some(_)) => match input.maybe(item.by_mut()) {
                Some(Some(value)) => Ok(Some(value)),
                Some(None) => {
                    *did_trail = true;
                    Ok(None)
                }
                None => Err(()),
            },
            Some(None) => Err(()),
            None => Err(()),
        }
    }
}

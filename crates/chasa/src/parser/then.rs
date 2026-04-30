use reborrow_generic::Reborrow;

use crate::Back as _;
use crate::back::RbBack;
use crate::error::ErrorSink;
use crate::input::{In, Input};
use crate::parser::{Parser, ParserMut, ParserOnce, SkipParser, SkipParserMut, SkipParserOnce};

pub struct Then<P, F>(P, F);

/// Run a parser and pass its output and input to a closure (`FnOnce`).
///
/// ```rust
/// use chasa::prelude::*;
///
/// let parser = then_once(item('a'), |c, i| {
///     if c == 'a' { item('b').parse_once(i) } else { None }
/// });
/// let out = "ab".test(parser);
/// assert_eq!(out, Some('b'));
/// ```
#[inline(always)]
pub fn then_once<P, I, N, L, E, F, O1, O2>(parser: P, f: F) -> Then<P, F>
where
    P: ParserOnce<I, N, L, E, Out = O1>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: FnOnce(O1, In<I, N, L, E>) -> Option<O2>,
{
    Then(parser, f)
}

/// Run a parser and pass its output and input to a closure (`FnMut`).
///
/// ```rust
/// use chasa::prelude::*;
///
/// let mut parser = then_mut(item('a'), |c, i| {
///     if c == 'a' { item('b').parse_once(i) } else { None }
/// });
/// let out = "ab".test(parser.by_mut());
/// assert_eq!(out, Some('b'));
/// ```
#[inline(always)]
pub fn then_mut<P, I, N, L, E, F, O1, O2>(parser: P, f: F) -> Then<P, F>
where
    P: ParserOnce<I, N, L, E, Out = O1>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: FnMut(O1, In<I, N, L, E>) -> Option<O2>,
{
    Then(parser, f)
}

/// Run a parser and pass its output and input to a closure (`Fn`).
///
/// ```rust
/// use chasa::prelude::*;
///
/// let parser = then(item('a'), |c, i| {
///     if c == 'a' { item('b').parse_once(i) } else { None }
/// });
/// let out = "ab".test(parser);
/// assert_eq!(out, Some('b'));
/// ```
#[inline(always)]
pub fn then<P, I, N, L, E, F, O1, O2>(parser: P, f: F) -> Then<P, F>
where
    P: ParserOnce<I, N, L, E, Out = O1>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: Fn(O1, In<I, N, L, E>) -> Option<O2>,
{
    Then(parser, f)
}

impl<P, F, I, N, L, E, O1, O2> SkipParserOnce<I, N, L, E> for Then<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E, Out = O1>,
    F: FnOnce(O1, In<I, N, L, E>) -> Option<O2>,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.parse_once(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, O1, O2> SkipParserMut<I, N, L, E> for Then<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = O1>,
    F: FnMut(O1, In<I, N, L, E>) -> Option<O2>,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.parse_mut(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, O1, O2> SkipParser<I, N, L, E> for Then<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = O1>,
    F: Fn(O1, In<I, N, L, E>) -> Option<O2>,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.parse(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, O1, O2> ParserOnce<I, N, L, E> for Then<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E, Out = O1>,
    F: FnOnce(O1, In<I, N, L, E>) -> Option<O2>,
{
    type Out = O2;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<O2> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            let o = self.0.parse_once(i.rb())?;
            self.1(o, i)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, O1, O2> ParserMut<I, N, L, E> for Then<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = O1>,
    F: FnMut(O1, In<I, N, L, E>) -> Option<O2>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<O2> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            let o = self.0.parse_mut(i.rb())?;
            self.1(o, i)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, O1, O2> Parser<I, N, L, E> for Then<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = O1>,
    F: Fn(O1, In<I, N, L, E>) -> Option<O2>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<O2> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            let o = self.0.parse(i.rb())?;
            self.1(o, i)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

/// Sequence two parsers and return a tuple.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ab".test(seq(item('a'), item('b')));
/// assert_eq!(out, Some(('a', 'b')));
///
/// let out = "aX".test(seq(item('a'), item('b')));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn seq<P, Q>(left: P, right: Q) -> (P, Q) {
    (left, right)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Left<P, Q>(P, Q);

/// Sequence two parsers and return the left output.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ab".test(left(item('a'), item('b')));
/// assert_eq!(out, Some('a'));
///
/// let out = "aX".test(left(item('a'), item('b')));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn left<P, Q>(p: P, q: Q) -> Left<P, Q> {
    Left(p, q)
}

impl<P, Q, I, N, L, E> SkipParserOnce<I, N, L, E> for Left<P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
    Q: SkipParserOnce<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.discard_once(i.rb())?;
            self.1.discard_once(i)?;
            Some(())
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, I, N, L, E> SkipParserMut<I, N, L, E> for Left<P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.discard_mut(i.rb())?;
            self.1.discard_mut(i)?;
            Some(())
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, I, N, L, E> SkipParser<I, N, L, E> for Left<P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
    Q: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.discard(i.rb())?;
            self.1.discard(i)?;
            Some(())
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, I, N, L, E, O> ParserOnce<I, N, L, E> for Left<P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E, Out = O>,
    Q: ParserOnce<I, N, L, E>,
{
    type Out = O;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            let out = self.0.parse_once(i.rb())?;
            self.1.parse_once(i)?;
            Some(out)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, I, N, L, E, O> ParserMut<I, N, L, E> for Left<P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E, Out = O>,
    Q: ParserMut<I, N, L, E>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            let out = self.0.parse_mut(i.rb())?;
            self.1.parse_mut(i)?;
            Some(out)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, I, N, L, E, O> Parser<I, N, L, E> for Left<P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E, Out = O>,
    Q: Parser<I, N, L, E>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            let out = self.0.parse(i.rb())?;
            self.1.parse(i)?;
            Some(out)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Right<P, Q>(P, Q);

/// Sequence two parsers and return the right output.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "ab".test(right(item('a'), item('b')));
/// assert_eq!(out, Some('b'));
///
/// let out = "aX".test(right(item('a'), item('b')));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn right<P, Q>(p: P, q: Q) -> Right<P, Q> {
    Right(p, q)
}

impl<P, Q, I, N, L, E> SkipParserOnce<I, N, L, E> for Right<P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
    Q: SkipParserOnce<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.discard_once(i.rb())?;
            self.1.discard_once(i)?;
            Some(())
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, I, N, L, E> SkipParserMut<I, N, L, E> for Right<P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.discard_mut(i.rb())?;
            self.1.discard_mut(i)?;
            Some(())
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, I, N, L, E> SkipParser<I, N, L, E> for Right<P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
    Q: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.discard(i.rb())?;
            self.1.discard(i)?;
            Some(())
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, I, N, L, E, O> ParserOnce<I, N, L, E> for Right<P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E>,
    Q: ParserOnce<I, N, L, E, Out = O>,
{
    type Out = O;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.parse_once(i.rb())?;
            self.1.parse_once(i)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, I, N, L, E, O> ParserMut<I, N, L, E> for Right<P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Q: ParserMut<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.parse_mut(i.rb())?;
            self.1.parse_mut(i)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, I, N, L, E, O> Parser<I, N, L, E> for Right<P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    Q: Parser<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.parse(i.rb())?;
            self.1.parse(i)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Map<P, F>(P, F);

/// Map the output of a parser.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "a".test(map(item('a'), |c| c as u8));
/// assert_eq!(out, Some(b'a'));
///
/// let out = "b".test(map(item('a'), |c| c as u8));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn map<P, F>(parser: P, f: F) -> Map<P, F> {
    Map(parser, f)
}

impl<P, F, I, N, L, E, O> SkipParserOnce<I, N, L, E> for Map<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E>,
    F: FnOnce(P::Out) -> O,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.parse_once(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, O> SkipParserMut<I, N, L, E> for Map<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    F: FnMut(P::Out) -> O,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.parse_mut(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, O> SkipParser<I, N, L, E> for Map<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    F: Fn(P::Out) -> O,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.parse(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, O> ParserOnce<I, N, L, E> for Map<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E>,
    F: FnOnce(P::Out) -> O,
{
    type Out = O;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.parse_once(i).map(self.1));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, O> ParserMut<I, N, L, E> for Map<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    F: FnMut(P::Out) -> O,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.parse_mut(i).map(&mut self.1));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, O> Parser<I, N, L, E> for Map<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    F: Fn(P::Out) -> O,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.parse(i).map(&self.1));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Bind<P, F>(P, F);

/// Bind a parser and continue with the next parser.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "a".test(bind(item('a'), |_| value(1)));
/// assert_eq!(out, Some(1));
///
/// let out = "b".test(bind(item('a'), |_| value(1)));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn bind<P, F>(parser: P, f: F) -> Bind<P, F> {
    Bind(parser, f)
}

impl<P, F, I, N, L, E, Q, O> SkipParserOnce<I, N, L, E> for Bind<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E>,
    F: FnOnce(P::Out) -> Q,
    Q: ParserOnce<I, N, L, E, Out = O>,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.parse_once(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, Q, O> SkipParserMut<I, N, L, E> for Bind<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    F: FnMut(P::Out) -> Q,
    Q: ParserOnce<I, N, L, E, Out = O>,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.parse_mut(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, Q, O> SkipParser<I, N, L, E> for Bind<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    F: Fn(P::Out) -> Q,
    Q: ParserOnce<I, N, L, E, Out = O>,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.parse(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, Q, O> ParserOnce<I, N, L, E> for Bind<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E>,
    F: FnOnce(P::Out) -> Q,
    Q: ParserOnce<I, N, L, E, Out = O>,
{
    type Out = O;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            let out = self.0.parse_once(i.rb())?;
            (self.1)(out).parse_once(i)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, Q, O> ParserMut<I, N, L, E> for Bind<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    F: FnMut(P::Out) -> Q,
    Q: ParserOnce<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            let out = self.0.parse_mut(i.rb())?;
            (self.1)(out).parse_once(i)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, F, I, N, L, E, Q, O> Parser<I, N, L, E> for Bind<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    F: Fn(P::Out) -> Q,
    Q: ParserOnce<I, N, L, E, Out = O>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            let out = self.0.parse(i.rb())?;
            (self.1)(out).parse_once(i)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AndThen<P, F>(P, F);

/// Map with a fallible function (`FnOnce`).
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out =
///     "a".test(and_then_once(item('a'), |c| (c == 'a').then_some(1)));
/// assert_eq!(out, Some(1));
/// ```
#[inline(always)]
pub fn and_then_once<P, I, N, L, E, F, O>(parser: P, f: F) -> AndThen<P, F>
where
    P: ParserOnce<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: FnOnce(P::Out) -> Option<O>,
{
    AndThen(parser, f)
}

/// Map with a fallible function (`FnMut`).
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out =
///     "a".test(and_then_mut(item('a'), |c| (c == 'a').then_some(1)));
/// assert_eq!(out, Some(1));
/// ```
#[inline(always)]
pub fn and_then_mut<P, I, N, L, E, F, O>(parser: P, f: F) -> AndThen<P, F>
where
    P: ParserOnce<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: FnMut(P::Out) -> Option<O>,
{
    AndThen(parser, f)
}

/// Map with a fallible function (`Fn`).
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out =
///     "a".test(and_then(item('a'), |c| (c == 'a').then_some(1)));
/// assert_eq!(out, Some(1));
/// ```
#[inline(always)]
pub fn and_then<P, I, N, L, E, F, O>(parser: P, f: F) -> AndThen<P, F>
where
    P: ParserOnce<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    F: Fn(P::Out) -> Option<O>,
{
    AndThen(parser, f)
}

impl<P, I, N, L, E, F, O> SkipParserOnce<I, N, L, E> for AndThen<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E>,
    F: FnOnce(P::Out) -> Option<O>,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.parse_once(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, I, N, L, E, F, O> SkipParserMut<I, N, L, E> for AndThen<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    F: FnMut(P::Out) -> Option<O>,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.parse_mut(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, I, N, L, E, F, O> SkipParser<I, N, L, E> for AndThen<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    F: Fn(P::Out) -> Option<O>,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.parse(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, I, N, L, E, F, O> ParserOnce<I, N, L, E> for AndThen<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E>,
    F: FnOnce(P::Out) -> Option<O>,
{
    type Out = O;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.parse_once(i).and_then(self.1));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, I, N, L, E, F, O> ParserMut<I, N, L, E> for AndThen<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    F: FnMut(P::Out) -> Option<O>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.parse_mut(i).and_then(|out| (self.1)(out)));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, I, N, L, E, F, O> Parser<I, N, L, E> for AndThen<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    F: Fn(P::Out) -> Option<O>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.parse(i).and_then(|out| (self.1)(out)));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Between<P, Q, R>(P, Q, R);

/// Parse between two delimiters.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out =
///     "(a)".test(between(item('('), item(')'), item('a')));
/// assert_eq!(out, Some('a'));
///
/// let out =
///     "(b)".test(between(item('('), item(')'), item('a')));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn between<P, Q, R>(left: P, right: R, inner: Q) -> Between<P, Q, R> {
    Between(left, inner, right)
}

impl<P, Q, R, I, N, L, E> SkipParserOnce<I, N, L, E> for Between<P, Q, R>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
    Q: SkipParserOnce<I, N, L, E>,
    R: SkipParserOnce<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.discard_once(i.rb())?;
            self.1.discard_once(i.rb())?;
            self.2.discard_once(i)?;
            Some(())
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, R, I, N, L, E> SkipParserMut<I, N, L, E> for Between<P, Q, R>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    R: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.discard_mut(i.rb())?;
            self.1.discard_mut(i.rb())?;
            self.2.discard_mut(i)?;
            Some(())
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, R, I, N, L, E> SkipParser<I, N, L, E> for Between<P, Q, R>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
    Q: SkipParser<I, N, L, E>,
    R: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.discard(i.rb())?;
            self.1.discard(i.rb())?;
            self.2.discard(i)?;
            Some(())
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, R, I, N, L, E, O> ParserOnce<I, N, L, E> for Between<P, Q, R>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserOnce<I, N, L, E>,
    Q: ParserOnce<I, N, L, E, Out = O>,
    R: ParserOnce<I, N, L, E>,
{
    type Out = O;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.parse_once(i.rb())?;
            let out = self.1.parse_once(i.rb())?;
            self.2.parse_once(i)?;
            Some(out)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, R, I, N, L, E, O> ParserMut<I, N, L, E> for Between<P, Q, R>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Q: ParserMut<I, N, L, E, Out = O>,
    R: ParserMut<I, N, L, E>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.parse_mut(i.rb())?;
            let out = self.1.parse_mut(i.rb())?;
            self.2.parse_mut(i)?;
            Some(out)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, Q, R, I, N, L, E, O> Parser<I, N, L, E> for Between<P, Q, R>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    Q: Parser<I, N, L, E, Out = O>,
    R: Parser<I, N, L, E>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|mut i| {
            self.0.parse(i.rb())?;
            let out = self.1.parse(i.rb())?;
            self.2.parse(i)?;
            Some(out)
        });
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct To<P, O>(P, O);

/// Ignore the parser output and return a constant value.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "a".test(to(item('a'), 123));
/// assert_eq!(out, Some(123));
///
/// let out = "b".test(to(item('a'), 123));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn to<P, O>(parser: P, value: O) -> To<P, O> {
    To(parser, value)
}

impl<P, O, I, N, L, E> SkipParserOnce<I, N, L, E> for To<P, O>
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
        let (out, is_cut) = i.capture_cut(|i| self.0.discard_once(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, O, I, N, L, E> SkipParserMut<I, N, L, E> for To<P, O>
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
        let (out, is_cut) = i.capture_cut(|i| self.0.discard_mut(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, O, I, N, L, E> SkipParser<I, N, L, E> for To<P, O>
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
        let (out, is_cut) = i.capture_cut(|i| self.0.discard(i));
        if out.is_some() || is_cut {
            return out.map(|_| ());
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, O, I, N, L, E> ParserOnce<I, N, L, E> for To<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
{
    type Out = O;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.discard_once(i).map(|_| self.1));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, O, I, N, L, E> ParserMut<I, N, L, E> for To<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
    O: Clone,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.discard_mut(i).map(|_| self.1.clone()));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, O, I, N, L, E> Parser<I, N, L, E> for To<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
    O: Clone,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<O> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.discard(i).map(|_| self.1.clone()));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Skip<P>(P);

/// Run a parser and drop its output.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "a".test(skip(item('a')));
/// assert_eq!(out, Some(()));
///
/// let out = "b".test(skip(item('a')));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn skip<P>(parser: P) -> Skip<P> {
    Skip(parser)
}

impl<P, I, N, L, E> SkipParserOnce<I, N, L, E> for Skip<P>
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
        let (out, is_cut) = i.capture_cut(|i| self.0.discard_once(i).map(|_| ()));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, I, N, L, E> SkipParserMut<I, N, L, E> for Skip<P>
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
        let (out, is_cut) = i.capture_cut(|i| self.0.discard_mut(i).map(|_| ()));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, I, N, L, E> SkipParser<I, N, L, E> for Skip<P>
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
        let (out, is_cut) = i.capture_cut(|i| self.0.discard(i).map(|_| ()));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, I, N, L, E> ParserOnce<I, N, L, E> for Skip<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserOnce<I, N, L, E>,
{
    type Out = ();
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.discard_once(i).map(|_| ()));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, I, N, L, E> ParserMut<I, N, L, E> for Skip<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.discard_mut(i).map(|_| ()));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

impl<P, I, N, L, E> Parser<I, N, L, E> for Skip<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let checkpoint = i.checkpoint();
        let (out, is_cut) = i.capture_cut(|i| self.0.discard(i).map(|_| ()));
        if out.is_some() || is_cut {
            return out;
        }
        i.rollback(checkpoint);
        None
    }
}

use core::marker::PhantomData;

use reborrow_generic::Reborrow;

use crate::Back as _;
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

#[inline]
fn maybe_skip<P, I, N, L, E>(i: &mut In<I, N, L, E>, parser: &mut P) -> Option<Option<()>>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    let checkpoint = i.checkpoint();
    let errors_checkpoint = i.errors_checkpoint();
    match i.capture_cut(|i| parser.discard_mut(i)) {
        (Some(_), _) => Some(Some(())),
        (None, true) => None,
        (None, false) => {
            i.errors_rollback(errors_checkpoint);
            i.rollback(checkpoint);
            Some(None)
        }
    }
}

#[inline]
fn maybe_skip_ref<P, I, N, L, E>(i: &mut In<I, N, L, E>, parser: &P) -> Option<Option<()>>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    let checkpoint = i.checkpoint();
    let errors_checkpoint = i.errors_checkpoint();
    match i.capture_cut(|i| parser.discard(i)) {
        (Some(_), _) => Some(Some(())),
        (None, true) => None,
        (None, false) => {
            i.errors_rollback(errors_checkpoint);
            i.rollback(checkpoint);
            Some(None)
        }
    }
}

pub struct ManyIterator<'a, P, I, N, L, E, O>
where
    P: ParserMut<I, N, L, E, Out = O>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    pub(crate) parser: P,
    pub(crate) i: In<'a, I, N, L, E>,
    pub(crate) is_end: bool,
    pub(crate) hard_failure: &'a mut bool,
    pub(crate) _marker: PhantomData<fn() -> O>,
}

impl<'a, P, I, N, L, E, O> Iterator for ManyIterator<'a, P, I, N, L, E, O>
where
    P: ParserMut<I, N, L, E, Out = O>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    type Item = O;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.is_end || *self.hard_failure {
            None
        } else {
            match maybe(&mut self.i, &mut self.parser) {
                Some(Some(o)) => Some(o),
                Some(None) => {
                    self.is_end = true;
                    None
                }
                None => {
                    *self.hard_failure = true;
                    None
                }
            }
        }
    }
}

pub type ManyMapIterator<'a, 'b, P, I, N, L, E, O> =
    ManyIterator<'a, RefOrMutParser<'b, P, I, N, L, E>, I, N, L, E, O>;

pub struct Many<P, O>(P, PhantomData<fn() -> O>);

/// Parse zero or more items and collect them.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out: Option<String> = "aaab".test(many(item('a')));
/// assert_eq!(out, Some("aaa".to_string()));
///
/// let out: Option<String> = "bbb".test(many(item('a')));
/// assert_eq!(out, Some("".to_string()));
///
/// let hard = many(right(cut, item('a')));
/// let out: Option<String> = "b".test(hard);
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn many<P, O>(parser: P) -> Many<P, O> {
    Many(parser, PhantomData)
}

impl<P, I, N, L, E, O> SkipParserOnce<I, N, L, E> for Many<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let mut parser = self.0;
        loop {
            match maybe_skip(&mut i, &mut parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

impl<P, I, N, L, E, O> SkipParserMut<I, N, L, E> for Many<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let parser = &mut self.0;
        loop {
            match maybe_skip(&mut i, parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

impl<P, I, N, L, E, O> SkipParser<I, N, L, E> for Many<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let parser = &self.0;
        loop {
            match maybe_skip_ref(&mut i, parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

impl<P, I, N, L, E, O> ParserOnce<I, N, L, E> for Many<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    type Out = O;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<O> {
        let parser = self.0;
        let mut hard_failure = false;
        let it = ManyIterator {
            parser,
            i: i.rb(),
            is_end: false,
            hard_failure: &mut hard_failure,
            _marker: PhantomData,
        };
        let out = it.collect();
        if hard_failure { None } else { Some(out) }
    }
}

impl<P, I, N, L, E, O> ParserMut<I, N, L, E> for Many<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<O> {
        let mut hard_failure = false;
        let it = ManyIterator {
            parser: RefOrMutParser::new_mut(&mut self.0),
            i: i.rb(),
            is_end: false,
            hard_failure: &mut hard_failure,
            _marker: PhantomData,
        };
        let out = it.collect();
        if hard_failure { None } else { Some(out) }
    }
}

impl<P, I, N, L, E, O> Parser<I, N, L, E> for Many<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<O> {
        let mut hard_failure = false;
        let it = ManyIterator {
            parser: RefOrMutParser::new_ref(&self.0),
            i: i.rb(),
            is_end: false,
            hard_failure: &mut hard_failure,
            _marker: PhantomData,
        };
        let out = it.collect();
        if hard_failure { None } else { Some(out) }
    }
}

pub struct Many1<P, O>(P, PhantomData<fn() -> O>);

/// Parse one or more items and collect them.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out: Option<String> = "aaab".test(many1(item('a')));
/// assert_eq!(out, Some("aaa".to_string()));
///
/// let out: Option<String> = "bbb".test(many1(item('a')));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn many1<P, O>(parser: P) -> Many1<P, O> {
    Many1(parser, PhantomData)
}

impl<P, I, N, L, E, O> SkipParserOnce<I, N, L, E> for Many1<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let mut parser = self.0;
        match maybe_skip(&mut i, &mut parser) {
            Some(Some(())) => {}
            Some(None) => return None,
            None => return None,
        }
        loop {
            match maybe_skip(&mut i, &mut parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

impl<P, I, N, L, E, O> SkipParserMut<I, N, L, E> for Many1<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let parser = &mut self.0;
        match maybe_skip(&mut i, parser) {
            Some(Some(())) => {}
            Some(None) => return None,
            None => return None,
        }
        loop {
            match maybe_skip(&mut i, parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

impl<P, I, N, L, E, O> SkipParser<I, N, L, E> for Many1<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let parser = &self.0;
        match maybe_skip_ref(&mut i, parser) {
            Some(Some(())) => {}
            Some(None) => return None,
            None => return None,
        }
        loop {
            match maybe_skip_ref(&mut i, parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

impl<P, I, N, L, E, O> ParserOnce<I, N, L, E> for Many1<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    type Out = O;
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<O> {
        let mut parser = self.0;
        let first = match maybe(&mut i, &mut parser) {
            Some(Some(value)) => value,
            Some(None) => return None,
            None => return None,
        };
        let mut hard_failure = false;
        let it = ManyIterator {
            parser,
            i: i.rb(),
            is_end: false,
            hard_failure: &mut hard_failure,
            _marker: PhantomData,
        };
        let out = core::iter::once(first).chain(it).collect();
        if hard_failure { None } else { Some(out) }
    }
}

impl<P, I, N, L, E, O> ParserMut<I, N, L, E> for Many1<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<O> {
        let mut parser = RefOrMutParser::new_mut(&mut self.0);
        let first = match maybe(&mut i, &mut parser) {
            Some(Some(value)) => value,
            Some(None) => return None,
            None => return None,
        };
        let mut hard_failure = false;
        let it = ManyIterator {
            parser,
            i: i.rb(),
            is_end: false,
            hard_failure: &mut hard_failure,
            _marker: PhantomData,
        };
        let out = core::iter::once(first).chain(it).collect();
        if hard_failure { None } else { Some(out) }
    }
}

impl<P, I, N, L, E, O> Parser<I, N, L, E> for Many1<P, O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<O> {
        let mut parser = RefOrMutParser::new_ref(&self.0);
        let first = match maybe(&mut i, &mut parser) {
            Some(Some(value)) => value,
            Some(None) => return None,
            None => return None,
        };
        let mut hard_failure = false;
        let it = ManyIterator {
            parser,
            i: i.rb(),
            is_end: false,
            hard_failure: &mut hard_failure,
            _marker: PhantomData,
        };
        let out = core::iter::once(first).chain(it).collect();
        if hard_failure { None } else { Some(out) }
    }
}

pub struct SkipMany<P>(P);

/// Parse zero or more items and drop the results.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "aaab".test(many_skip(item('a')));
/// assert_eq!(out, Some(()));
///
/// let out = "bbb".test(many_skip(item('a')));
/// assert_eq!(out, Some(()));
///
/// let hard = many_skip(right(cut, item('a')));
/// let out = "b".test(hard);
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn many_skip<P>(parser: P) -> SkipMany<P> {
    SkipMany(parser)
}

impl<P, I, N, L, E> SkipParserOnce<I, N, L, E> for SkipMany<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_once(i).map(|_| ())
    }
}

impl<P, I, N, L, E> SkipParserMut<I, N, L, E> for SkipMany<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_mut(i).map(|_| ())
    }
}

impl<P, I, N, L, E> SkipParser<I, N, L, E> for SkipMany<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.parse(i).map(|_| ())
    }
}

impl<P, I, N, L, E> ParserOnce<I, N, L, E> for SkipMany<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    type Out = ();
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let mut parser = self.0;
        loop {
            match maybe_skip(&mut i, &mut parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

impl<P, I, N, L, E> ParserMut<I, N, L, E> for SkipMany<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let parser = &mut self.0;
        loop {
            match maybe_skip(&mut i, parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

impl<P, I, N, L, E> Parser<I, N, L, E> for SkipMany<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let parser = &self.0;
        loop {
            match maybe_skip_ref(&mut i, parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

#[derive(Clone, Copy)]
pub struct SkipMany1<P>(P);

/// Parse one or more items and drop the results.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out = "aaab".test(many1_skip(item('a')));
/// assert_eq!(out, Some(()));
///
/// let out = "".test(many1_skip(item('a')));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn many1_skip<P>(parser: P) -> SkipMany1<P> {
    SkipMany1(parser)
}

impl<P, I, N, L, E> SkipParserOnce<I, N, L, E> for SkipMany1<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_once(i).map(|_| ())
    }
}

impl<P, I, N, L, E> SkipParserMut<I, N, L, E> for SkipMany1<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_mut(i).map(|_| ())
    }
}

impl<P, I, N, L, E> SkipParser<I, N, L, E> for SkipMany1<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.parse(i).map(|_| ())
    }
}

impl<P, I, N, L, E> ParserOnce<I, N, L, E> for SkipMany1<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    type Out = ();
    #[inline]
    fn parse_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let mut parser = self.0;
        match maybe_skip(&mut i, &mut parser) {
            Some(Some(())) => {}
            Some(None) => return None,
            None => return None,
        }
        loop {
            match maybe_skip(&mut i, &mut parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

impl<P, I, N, L, E> ParserMut<I, N, L, E> for SkipMany1<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParserMut<I, N, L, E>,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let parser = &mut self.0;
        match maybe_skip(&mut i, parser) {
            Some(Some(())) => {}
            Some(None) => return None,
            None => return None,
        }
        loop {
            match maybe_skip(&mut i, parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

impl<P, I, N, L, E> Parser<I, N, L, E> for SkipMany1<P>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: SkipParser<I, N, L, E>,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let parser = &self.0;
        match maybe_skip_ref(&mut i, parser) {
            Some(Some(())) => {}
            Some(None) => return None,
            None => return None,
        }
        loop {
            match maybe_skip_ref(&mut i, parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

pub struct ManyMap<P, F>(P, F);

/// Parse zero or more items and map an iterator.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out: Option<usize> =
///     "aaab".test(many_map(item('a'), |it| it.count()));
/// assert_eq!(out, Some(3));
///
/// let hard = many_map(right(cut, item('a')), |it| it.count());
/// let out: Option<usize> = "b".test(hard);
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn many_map<P, I, N, L, E, F, O>(parser: P, f: F) -> ManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    F: FnOnce(ManyMapIterator<P, I, N, L, E, P::Out>) -> O,
{
    ManyMap(parser, f)
}

/// Like `many_map`, but explicitly accepts `FnOnce`.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out: Option<usize> =
///     "aaab".test(many_map_once(item('a'), |it| it.count()));
/// assert_eq!(out, Some(3));
///
/// let out: Option<usize> =
///     "bbb".test(many_map_once(item('a'), |it| it.count()));
/// assert_eq!(out, Some(0));
///
/// let hard = many_map_once(right(cut, item('a')), |it| it.count());
/// let out: Option<usize> = "b".test(hard);
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn many_map_once<P, I, N, L, E, F, O>(parser: P, f: F) -> ManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    F: FnOnce(ManyMapIterator<P, I, N, L, E, P::Out>) -> O,
{
    ManyMap(parser, f)
}

/// Like `many_map`, but accepts `FnMut`.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let out: Option<usize> =
///     "aaab".test(many_map_mut(item('a'), |it| it.count()));
/// assert_eq!(out, Some(3));
///
/// let out: Option<usize> =
///     "bbb".test(many_map_mut(item('a'), |it| it.count()));
/// assert_eq!(out, Some(0));
///
/// let hard = many_map_mut(right(cut, item('a')), |it| it.count());
/// let out: Option<usize> = "b".test(hard);
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn many_map_mut<P, I, N, L, E, F, O>(parser: P, f: F) -> ManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    F: FnMut(ManyMapIterator<P, I, N, L, E, P::Out>) -> O,
{
    ManyMap(parser, f)
}

impl<P, F, I, N, L, E, O> SkipParserOnce<I, N, L, E> for ManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    F: FnOnce(ManyMapIterator<P, I, N, L, E, P::Out>) -> O,
{
    #[inline]
    fn discard_once(self, mut i: In<I, N, L, E>) -> Option<()> {
        let mut parser = self.0;
        loop {
            match maybe_skip(&mut i, &mut parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

impl<P, F, I, N, L, E, O> SkipParserMut<I, N, L, E> for ManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    F: FnMut(ManyMapIterator<P, I, N, L, E, P::Out>) -> O,
{
    #[inline]
    fn discard_mut(&mut self, mut i: In<I, N, L, E>) -> Option<()> {
        let parser = &mut self.0;
        loop {
            match maybe_skip(&mut i, parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

impl<P, F, I, N, L, E, O> SkipParser<I, N, L, E> for ManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    F: Fn(ManyMapIterator<P, I, N, L, E, P::Out>) -> O,
{
    #[inline]
    fn discard(&self, mut i: In<I, N, L, E>) -> Option<()> {
        let parser = &self.0;
        loop {
            match maybe_skip_ref(&mut i, parser) {
                Some(Some(())) => {}
                Some(None) => break,
                None => return None,
            }
        }
        Some(())
    }
}

impl<P, F, I, N, L, E, O> ParserOnce<I, N, L, E> for ManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    F: FnOnce(ManyMapIterator<P, I, N, L, E, P::Out>) -> O,
{
    type Out = O;
    #[inline]
    fn parse_once(mut self, mut i: In<I, N, L, E>) -> Option<O> {
        let mut hard_failure = false;
        let it = ManyIterator {
            parser: RefOrMutParser::new_mut(&mut self.0),
            i: i.rb(),
            is_end: false,
            hard_failure: &mut hard_failure,
            _marker: PhantomData,
        };
        let out = (self.1)(it);
        if hard_failure { None } else { Some(out) }
    }
}

impl<P, F, I, N, L, E, O> ParserMut<I, N, L, E> for ManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    F: FnMut(ManyMapIterator<P, I, N, L, E, P::Out>) -> O,
{
    #[inline]
    fn parse_mut(&mut self, mut i: In<I, N, L, E>) -> Option<O> {
        let mut hard_failure = false;
        let it = ManyIterator {
            parser: RefOrMutParser::new_mut(&mut self.0),
            i: i.rb(),
            is_end: false,
            hard_failure: &mut hard_failure,
            _marker: PhantomData,
        };
        let out = (self.1)(it);
        if hard_failure { None } else { Some(out) }
    }
}

impl<P, F, I, N, L, E, O> Parser<I, N, L, E> for ManyMap<P, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    F: Fn(ManyMapIterator<P, I, N, L, E, P::Out>) -> O,
{
    #[inline]
    fn parse(&self, mut i: In<I, N, L, E>) -> Option<O> {
        let mut hard_failure = false;
        let it = ManyIterator {
            parser: RefOrMutParser::new_ref(&self.0),
            i: i.rb(),
            is_end: false,
            hard_failure: &mut hard_failure,
            _marker: PhantomData,
        };
        let out = (self.1)(it);
        if hard_failure { None } else { Some(out) }
    }
}

use core::marker::PhantomData;

use reborrow_generic::Reborrow;

use crate::back::RbBack;
use crate::error::ErrorSink;
use crate::input::{In, Input};
use crate::parser::prim::{RefOrMutParser, RefOrMutSkipParser};
use crate::parser::{Parser, ParserMut, ParserOnce, SkipParser, SkipParserMut, SkipParserOnce};

pub mod iter;

use iter::{Count, Trailing};

pub struct SepIterator<'a, P, Q, I, N, L, E, O, Co: Count, Tr: Trailing>
where
    P: ParserMut<I, N, L, E, Out = O>,
    Q: SkipParserMut<I, N, L, E>,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
{
    pub(crate) is_first: bool,
    pub(crate) item: P,
    pub(crate) sep: Q,
    pub(crate) input: In<'a, I, N, L, E>,
    pub(crate) is_end: bool,
    pub(crate) did_trail: &'a mut bool,
    pub(crate) hard_failure: &'a mut bool,
    pub(crate) _mode: PhantomData<fn() -> (Co, Tr)>,
    pub(crate) _marker: PhantomData<fn() -> O>,
}

pub type SepMapIterator<'a, 'b, P, Q, I, N, L, E, O, Co, Tr> = SepIterator<
    'a,
    RefOrMutParser<'b, P, I, N, L, E>,
    RefOrMutSkipParser<'b, Q, I, N, L, E>,
    I,
    N,
    L,
    E,
    O,
    Co,
    Tr,
>;

impl<'a, P, Q, I, N, L, E, O, Co, Tr> Iterator for SepIterator<'a, P, Q, I, N, L, E, O, Co, Tr>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: ParserMut<I, N, L, E, Out = O>,
    Q: SkipParserMut<I, N, L, E>,
{
    type Item = O;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.is_end || *self.hard_failure {
            return None;
        }

        if self.is_first {
            self.is_first = false;
            match Co::first(&mut self.input, &mut self.item) {
                Ok(Some(item)) => return Some(item),
                Ok(None) => {
                    self.is_end = true;
                    return None;
                }
                Err(()) => {
                    *self.hard_failure = true;
                    self.is_end = true;
                    return None;
                }
            }
        }

        match Tr::second(
            &mut self.input,
            &mut self.sep,
            &mut self.item,
            &mut *self.did_trail,
        ) {
            Ok(Some(item)) => Some(item),
            Ok(None) => {
                self.is_end = true;
                None
            }
            Err(()) => {
                *self.hard_failure = true;
                self.is_end = true;
                None
            }
        }
    }
}

impl<'a, P, Q, I, N, L, E, O, Co, Tr> SepIterator<'a, P, Q, I, N, L, E, O, Co, Tr>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: ParserMut<I, N, L, E, Out = O>,
    Q: SkipParserMut<I, N, L, E>,
{
    /// Require at least one item when iterating.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let comma = to(item(','), ());
    /// let out: Option<usize> =
    ///     "a,a".test(sep_map(item('a'), comma, |it| it.one().count()));
    /// assert_eq!(out, Some(2));
    ///
    /// let comma = to(item(','), ());
    /// let out: Option<usize> =
    ///     "".test(sep_map(item('a'), comma, |it| it.one().count()));
    /// assert_eq!(out, None);
    /// ```
    #[inline]
    pub fn one(self) -> SepIterator<'a, P, Q, I, N, L, E, O, iter::One, Tr> {
        SepIterator {
            is_first: self.is_first,
            item: self.item,
            sep: self.sep,
            input: self.input,
            is_end: self.is_end,
            did_trail: self.did_trail,
            hard_failure: self.hard_failure,
            _mode: PhantomData,
            _marker: PhantomData,
        }
    }

    /// Reject a trailing separator when iterating.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let comma = to(item(','), ());
    /// let out: Option<usize> =
    ///     "a,a".test(sep_map(item('a'), comma, |it| it.no_trail().count()));
    /// assert_eq!(out, Some(2));
    ///
    /// let comma = to(item(','), ());
    /// let out: Option<usize> =
    ///     "a,a,".test(sep_map(item('a'), comma, |it| it.no_trail().count()));
    /// assert_eq!(out, None);
    /// ```
    #[inline]
    pub fn no_trail(self) -> SepIterator<'a, P, Q, I, N, L, E, O, Co, iter::No> {
        SepIterator {
            is_first: self.is_first,
            item: self.item,
            sep: self.sep,
            input: self.input,
            is_end: self.is_end,
            did_trail: self.did_trail,
            hard_failure: self.hard_failure,
            _mode: PhantomData,
            _marker: PhantomData,
        }
    }

    /// Require a trailing separator when iterating.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let comma = to(item(','), ());
    /// let out: Option<usize> =
    ///     "a,a,".test(sep_map(item('a'), comma, |it| it.must_trail().count()));
    /// assert_eq!(out, Some(2));
    ///
    /// let comma = to(item(','), ());
    /// let out: Option<usize> =
    ///     "a,a".test(sep_map(item('a'), comma, |it| it.must_trail().count()));
    /// assert_eq!(out, None);
    /// ```
    #[inline]
    pub fn must_trail(self) -> SepIterator<'a, P, Q, I, N, L, E, O, Co, iter::Must> {
        SepIterator {
            is_first: self.is_first,
            item: self.item,
            sep: self.sep,
            input: self.input,
            is_end: self.is_end,
            did_trail: self.did_trail,
            hard_failure: self.hard_failure,
            _mode: PhantomData,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Copy, Debug, Hash)]
pub struct Sep<O, Co, Tr, P, Q> {
    pub(crate) item: P,
    pub(crate) sep: Q,
    pub(crate) _marker: PhantomData<fn() -> (O, Co, Tr)>,
}

/// Parse zero or more items separated by a separator parser.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let comma = to(item(','), ());
/// let out: Option<String> = "a,a".test(sep(item('a'), comma));
/// assert_eq!(out, Some("aa".to_string()));
///
/// let comma = to(item(','), ());
/// let out: Option<String> = "".test(sep(item('a'), comma));
/// assert_eq!(out, Some("".to_string()));
/// ```
#[inline(always)]
pub fn sep<O, P, Q>(item: P, sep: Q) -> Sep<O, iter::Zero, iter::Allow, P, Q> {
    Sep {
        item,
        sep,
        _marker: PhantomData,
    }
}

/// Parse one or more items separated by a separator parser.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let comma = to(item(','), ());
/// let out: Option<String> = "a,a".test(sep1(item('a'), comma));
/// assert_eq!(out, Some("aa".to_string()));
///
/// let comma = to(item(','), ());
/// let out: Option<String> = "".test(sep1(item('a'), comma));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn sep1<O, P, Q>(item: P, sep: Q) -> Sep<O, iter::One, iter::Allow, P, Q> {
    Sep {
        item,
        sep,
        _marker: PhantomData,
    }
}

impl<O, Co, Tr, P, Q> Sep<O, Co, Tr, P, Q>
where
    Co: Count,
    Tr: Trailing,
{
    /// Require at least one item.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let comma = to(item(','), ());
    /// let out: Option<String> =
    ///     "a,a".test(sep(item('a'), comma).one());
    /// assert_eq!(out, Some("aa".to_string()));
    ///
    /// let comma = to(item(','), ());
    /// let out: Option<String> =
    ///     "".test(sep(item('a'), comma).one());
    /// assert_eq!(out, None);
    /// ```
    #[inline]
    pub fn one(self) -> Sep<O, iter::One, Tr, P, Q> {
        Sep {
            item: self.item,
            sep: self.sep,
            _marker: PhantomData,
        }
    }

    /// Reject a trailing separator.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let comma = to(item(','), ());
    /// let out: Option<String> =
    ///     "a,a".test(sep(item('a'), comma).no_trail());
    /// assert_eq!(out, Some("aa".to_string()));
    ///
    /// let comma = to(item(','), ());
    /// let out: Option<String> =
    ///     "a,a,".test(sep(item('a'), comma).no_trail());
    /// assert_eq!(out, None);
    /// ```
    #[inline]
    pub fn no_trail(self) -> Sep<O, Co, iter::No, P, Q> {
        Sep {
            item: self.item,
            sep: self.sep,
            _marker: PhantomData,
        }
    }

    /// Require a trailing separator.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let comma = to(item(','), ());
    /// let out: Option<String> =
    ///     "a,a,".test(sep(item('a'), comma).must_trail());
    /// assert_eq!(out, Some("aa".to_string()));
    ///
    /// let comma = to(item(','), ());
    /// let out: Option<String> =
    ///     "a,a".test(sep(item('a'), comma).must_trail());
    /// assert_eq!(out, None);
    /// ```
    #[inline]
    pub fn must_trail(self) -> Sep<O, Co, iter::Must, P, Q> {
        Sep {
            item: self.item,
            sep: self.sep,
            _marker: PhantomData,
        }
    }

    /// Return whether a trailing separator was present.
    ///
    /// ```rust
    /// use chasa::prelude::*;
    ///
    /// let comma = to(item(','), ());
    /// let out: Option<(String, bool)> =
    ///     "a,a,".test(sep(item('a'), comma).use_trail());
    /// assert_eq!(out, Some(("aa".to_string(), true)));
    ///
    /// let comma = to(item(','), ());
    /// let out: Option<(String, bool)> =
    ///     "".test(sep(item('a'), comma).one().use_trail());
    /// assert_eq!(out, None);
    /// ```
    #[inline]
    pub fn use_trail(self) -> UseTrailSep<O, Co, Tr, P, Q> {
        UseTrailSep(self)
    }
}

#[derive(Clone, Copy, Debug, Hash)]
pub struct UseTrailSep<O, Co, Tr, P, Q>(Sep<O, Co, Tr, P, Q>);

#[inline]
fn run_sep<P, Q, I, N, L, E, O, Co, Tr>(mut i: In<I, N, L, E>, item: P, sep: Q) -> Option<O>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
    Co: Count,
    Tr: Trailing,
{
    let mut hard_failure = false;
    let mut did_trail = false;
    let iter = SepIterator {
        is_first: true,
        item,
        sep,
        input: i.rb(),
        is_end: false,
        did_trail: &mut did_trail,
        hard_failure: &mut hard_failure,
        _mode: PhantomData::<fn() -> (Co, Tr)>,
        _marker: PhantomData,
    };
    let out: O = iter.collect();
    if hard_failure || !Tr::validate_end(did_trail) {
        None
    } else {
        Some(out)
    }
}

#[inline]
fn run_sep_use_trail<P, Q, I, N, L, E, O, Co, Tr>(
    mut i: In<I, N, L, E>,
    item: P,
    sep: Q,
) -> Option<(O, bool)>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
    Co: Count,
    Tr: Trailing,
{
    let mut hard_failure = false;
    let mut did_trail = false;
    let iter = SepIterator {
        is_first: true,
        item,
        sep,
        input: i.rb(),
        is_end: false,
        did_trail: &mut did_trail,
        hard_failure: &mut hard_failure,
        _mode: PhantomData::<fn() -> (Co, Tr)>,
        _marker: PhantomData,
    };
    let out: O = iter.collect();
    if hard_failure || !Tr::validate_end(did_trail) {
        None
    } else {
        Some((out, did_trail))
    }
}

impl<O, Co, Tr, P, Q, I, N, L, E> SkipParserOnce<I, N, L, E> for Sep<O, Co, Tr, P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_once(i).map(|_| ())
    }
}

impl<O, Co, Tr, P, Q, I, N, L, E> SkipParserMut<I, N, L, E> for Sep<O, Co, Tr, P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_mut(i).map(|_| ())
    }
}

impl<O, Co, Tr, P, Q, I, N, L, E> SkipParser<I, N, L, E> for Sep<O, Co, Tr, P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: Parser<I, N, L, E>,
    Q: SkipParser<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.parse(i).map(|_| ())
    }
}

impl<O, Co, Tr, P, Q, I, N, L, E> ParserOnce<I, N, L, E> for Sep<O, Co, Tr, P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    type Out = O;
    #[inline]
    fn parse_once(self, i: In<I, N, L, E>) -> Option<O> {
        run_sep::<_, _, _, _, _, _, _, Co, Tr>(i, self.item, self.sep)
    }
}

impl<O, Co, Tr, P, Q, I, N, L, E> ParserMut<I, N, L, E> for Sep<O, Co, Tr, P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<O> {
        run_sep::<_, _, _, _, _, _, _, Co, Tr>(i, self.item.by_mut(), self.sep.by_mut())
    }
}

impl<O, Co, Tr, P, Q, I, N, L, E> Parser<I, N, L, E> for Sep<O, Co, Tr, P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: Parser<I, N, L, E>,
    Q: SkipParser<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<O> {
        run_sep::<_, _, _, _, _, _, _, Co, Tr>(i, self.item.by_ref(), self.sep.by_ref())
    }
}

impl<O, Co, Tr, P, Q, I, N, L, E> SkipParserOnce<I, N, L, E> for UseTrailSep<O, Co, Tr, P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_once(i).map(|_| ())
    }
}

impl<O, Co, Tr, P, Q, I, N, L, E> SkipParserMut<I, N, L, E> for UseTrailSep<O, Co, Tr, P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_mut(i).map(|_| ())
    }
}

impl<O, Co, Tr, P, Q, I, N, L, E> SkipParser<I, N, L, E> for UseTrailSep<O, Co, Tr, P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: Parser<I, N, L, E>,
    Q: SkipParser<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.parse(i).map(|_| ())
    }
}

impl<O, Co, Tr, P, Q, I, N, L, E> ParserOnce<I, N, L, E> for UseTrailSep<O, Co, Tr, P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    type Out = (O, bool);
    #[inline]
    fn parse_once(self, i: In<I, N, L, E>) -> Option<(O, bool)> {
        run_sep_use_trail::<_, _, _, _, _, _, _, Co, Tr>(i, self.0.item, self.0.sep)
    }
}

impl<O, Co, Tr, P, Q, I, N, L, E> ParserMut<I, N, L, E> for UseTrailSep<O, Co, Tr, P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<(O, bool)> {
        run_sep_use_trail::<_, _, _, _, _, _, _, Co, Tr>(
            i,
            self.0.item.by_mut(),
            self.0.sep.by_mut(),
        )
    }
}

impl<O, Co, Tr, P, Q, I, N, L, E> Parser<I, N, L, E> for UseTrailSep<O, Co, Tr, P, Q>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: Parser<I, N, L, E>,
    Q: SkipParser<I, N, L, E>,
    O: FromIterator<P::Out>,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<(O, bool)> {
        run_sep_use_trail::<_, _, _, _, _, _, _, Co, Tr>(
            i,
            self.0.item.by_ref(),
            self.0.sep.by_ref(),
        )
    }
}

pub struct SepMap<Co, Tr, P, Q, F> {
    pub(crate) item: P,
    pub(crate) sep: Q,
    pub(crate) f: F,
    pub(crate) _marker: PhantomData<fn() -> (Co, Tr)>,
}

/// Parse separated items and map them with an iterator.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let comma = to(item(','), ());
/// let out: Option<usize> =
///     "a,a".test(sep_map(item('a'), comma, |it| it.count()));
/// assert_eq!(out, Some(2));
///
/// let comma = to(item(','), ());
/// let out: Option<usize> =
///     "".test(sep_map(item('a'), comma, |it| it.one().count()));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn sep_map<P, Q, I, N, L, E, F, O>(
    item: P,
    sep: Q,
    f: F,
) -> SepMap<iter::Zero, iter::Allow, P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    F: FnOnce(SepMapIterator<P, Q, I, N, L, E, P::Out, iter::Zero, iter::Allow>) -> O,
{
    SepMap {
        item,
        sep,
        f,
        _marker: PhantomData,
    }
}

/// Like `sep_map`, but require at least one item.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let comma = to(item(','), ());
/// let out: Option<usize> =
///     "a,a".test(sep1_map(item('a'), comma, |it| it.count()));
/// assert_eq!(out, Some(2));
///
/// let comma = to(item(','), ());
/// let out: Option<usize> =
///     "".test(sep1_map(item('a'), comma, |it| it.count()));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn sep1_map<P, Q, I, N, L, E, F, O>(
    item: P,
    sep: Q,
    f: F,
) -> SepMap<iter::One, iter::Allow, P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    F: FnOnce(SepMapIterator<P, Q, I, N, L, E, P::Out, iter::One, iter::Allow>) -> O,
{
    SepMap {
        item,
        sep,
        f,
        _marker: PhantomData,
    }
}

/// Like `sep_map`, but explicitly accepts `FnOnce`.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let comma = to(item(','), ());
/// let out: Option<usize> =
///     "a,a".test(sep_map_once(item('a'), comma, |it| it.count()));
/// assert_eq!(out, Some(2));
///
/// let comma = to(item(','), ());
/// let out: Option<usize> =
///     "".test(sep_map_once(item('a'), comma, |it| it.one().count()));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn sep_map_once<P, Q, I, N, L, E, F, O>(
    item: P,
    sep: Q,
    f: F,
) -> SepMap<iter::Zero, iter::Allow, P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    F: FnOnce(SepMapIterator<P, Q, I, N, L, E, P::Out, iter::Zero, iter::Allow>) -> O,
{
    SepMap {
        item,
        sep,
        f,
        _marker: PhantomData,
    }
}

/// Like `sep_map`, but accepts `FnMut`.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let comma = to(item(','), ());
/// let out: Option<usize> =
///     "a,a".test(sep_map_mut(item('a'), comma, |it| it.count()));
/// assert_eq!(out, Some(2));
///
/// let comma = to(item(','), ());
/// let out: Option<usize> =
///     "".test(sep_map_mut(item('a'), comma, |it| it.one().count()));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn sep_map_mut<P, Q, I, N, L, E, F, O>(
    item: P,
    sep: Q,
    f: F,
) -> SepMap<iter::Zero, iter::Allow, P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    F: FnMut(SepMapIterator<P, Q, I, N, L, E, P::Out, iter::Zero, iter::Allow>) -> O,
{
    SepMap {
        item,
        sep,
        f,
        _marker: PhantomData,
    }
}

#[inline]
pub(crate) fn sep_map_run<P, Q, F, Co, Tr, O, I, N, L, E>(
    item: P,
    sep: Q,
    f: F,
    mut i: In<I, N, L, E>,
) -> Option<O>
where
    Co: Count,
    Tr: Trailing,
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    F: FnOnce(SepIterator<P, Q, I, N, L, E, P::Out, Co, Tr>) -> O,
{
    let mut hard_failure = false;
    let mut did_trail = false;
    let out = (f)(SepIterator {
        is_first: true,
        item,
        sep,
        input: i.rb(),
        is_end: false,
        did_trail: &mut did_trail,
        hard_failure: &mut hard_failure,
        _mode: PhantomData,
        _marker: PhantomData,
    });
    if hard_failure { None } else { Some(out) }
}

impl<Co, Tr, P, Q, F, I, N, L, E, O> SkipParserOnce<I, N, L, E> for SepMap<Co, Tr, P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    F: FnOnce(SepMapIterator<P, Q, I, N, L, E, P::Out, Co, Tr>) -> O,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_once(i).map(|_| ())
    }
}

impl<Co, Tr, P, Q, F, I, N, L, E, O> SkipParserMut<I, N, L, E> for SepMap<Co, Tr, P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    F: FnMut(SepMapIterator<P, Q, I, N, L, E, P::Out, Co, Tr>) -> O,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_mut(i).map(|_| ())
    }
}

impl<Co, Tr, P, Q, F, I, N, L, E, O> SkipParser<I, N, L, E> for SepMap<Co, Tr, P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: Parser<I, N, L, E>,
    Q: SkipParser<I, N, L, E>,
    F: Fn(SepMapIterator<P, Q, I, N, L, E, P::Out, Co, Tr>) -> O,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.parse(i).map(|_| ())
    }
}

impl<Co, Tr, P, Q, F, I, N, L, E, O> ParserOnce<I, N, L, E> for SepMap<Co, Tr, P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    F: FnOnce(SepMapIterator<P, Q, I, N, L, E, P::Out, Co, Tr>) -> O,
{
    type Out = O;
    #[inline]
    fn parse_once(mut self, i: In<I, N, L, E>) -> Option<O> {
        sep_map_run(
            RefOrMutParser::new_mut(&mut self.item),
            RefOrMutSkipParser::new_mut(&mut self.sep),
            self.f,
            i,
        )
    }
}

impl<Co, Tr, P, Q, F, I, N, L, E, O> ParserMut<I, N, L, E> for SepMap<Co, Tr, P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: ParserMut<I, N, L, E>,
    Q: SkipParserMut<I, N, L, E>,
    F: FnMut(SepMapIterator<P, Q, I, N, L, E, P::Out, Co, Tr>) -> O,
{
    #[inline]
    fn parse_mut(&mut self, i: In<I, N, L, E>) -> Option<O> {
        sep_map_run(
            RefOrMutParser::new_mut(&mut self.item),
            RefOrMutSkipParser::new_mut(&mut self.sep),
            &mut self.f,
            i,
        )
    }
}

impl<Co, Tr, P, Q, F, I, N, L, E, O> Parser<I, N, L, E> for SepMap<Co, Tr, P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    Co: Count,
    Tr: Trailing,
    P: Parser<I, N, L, E>,
    Q: SkipParser<I, N, L, E>,
    F: Fn(SepMapIterator<P, Q, I, N, L, E, P::Out, Co, Tr>) -> O,
{
    #[inline]
    fn parse(&self, i: In<I, N, L, E>) -> Option<O> {
        sep_map_run(
            RefOrMutParser::new_ref(&self.item),
            RefOrMutSkipParser::new_ref(&self.sep),
            &self.f,
            i,
        )
    }
}

#[derive(Clone, Copy, Debug, Hash)]
pub struct SepReduce<P, Q, F>(pub(crate) P, pub(crate) Q, pub(crate) F);

/// Reduce `term` separated by `op`.
///
/// ```rust
/// use chasa::prelude::*;
///
/// let plus = to(item('+'), ());
/// let term = to(item('a'), 1);
/// let out =
///     "a+a+a".test(sep_reduce(term, plus, |a, _, b| a + b));
/// assert_eq!(out, Some(3));
///
/// let plus = to(item('+'), ());
/// let term = to(item('a'), 1);
/// let out =
///     "".test(sep_reduce(term, plus, |a, _, b| a + b));
/// assert_eq!(out, None);
/// ```
#[inline(always)]
pub fn sep_reduce<P, Q, F>(term: P, op: Q, f: F) -> SepReduce<P, Q, F> {
    SepReduce(term, op, f)
}

impl<P, Q, F, I, N, L, E, Op> SkipParserOnce<I, N, L, E> for SepReduce<P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Q: ParserMut<I, N, L, E, Out = Op>,
    F: FnMut(P::Out, Op, P::Out) -> P::Out,
{
    #[inline]
    fn discard_once(self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_once(i).map(|_| ())
    }
}

impl<P, Q, F, I, N, L, E, Op> SkipParserMut<I, N, L, E> for SepReduce<P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Q: ParserMut<I, N, L, E, Out = Op>,
    F: FnMut(P::Out, Op, P::Out) -> P::Out,
{
    #[inline]
    fn discard_mut(&mut self, i: In<I, N, L, E>) -> Option<()> {
        self.parse_mut(i).map(|_| ())
    }
}

impl<P, Q, F, I, N, L, E, Op> SkipParser<I, N, L, E> for SepReduce<P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    Q: Parser<I, N, L, E, Out = Op>,
    F: Fn(P::Out, Op, P::Out) -> P::Out,
{
    #[inline]
    fn discard(&self, i: In<I, N, L, E>) -> Option<()> {
        self.parse(i).map(|_| ())
    }
}

impl<P, Q, F, I, N, L, E, Op> ParserOnce<I, N, L, E> for SepReduce<P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Q: ParserMut<I, N, L, E, Out = Op>,
    F: FnMut(P::Out, Op, P::Out) -> P::Out,
{
    type Out = P::Out;
    #[inline]
    fn parse_once(self, mut input: In<I, N, L, E>) -> Option<P::Out> {
        let mut term = self.0;
        let mut op = self.1;
        let mut f = self.2;
        let mut left = term.parse_mut(input.rb())?;
        loop {
            match input.maybe(op.by_mut()) {
                Some(Some(op_value)) => {
                    let right = term.parse_mut(input.rb())?;
                    left = f(left, op_value, right);
                }
                Some(None) => return Some(left),
                None => return None,
            }
        }
    }
}

impl<P, Q, F, I, N, L, E, Op> ParserMut<I, N, L, E> for SepReduce<P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: ParserMut<I, N, L, E>,
    Q: ParserMut<I, N, L, E, Out = Op>,
    F: FnMut(P::Out, Op, P::Out) -> P::Out,
{
    #[inline]
    fn parse_mut(&mut self, mut input: In<I, N, L, E>) -> Option<P::Out> {
        let mut left = self.0.parse_mut(input.rb())?;
        loop {
            match input.maybe(self.1.by_mut()) {
                Some(Some(op_value)) => {
                    let right = self.0.parse_mut(input.rb())?;
                    left = (self.2)(left, op_value, right);
                }
                Some(None) => return Some(left),
                None => return None,
            }
        }
    }
}

impl<P, Q, F, I, N, L, E, Op> Parser<I, N, L, E> for SepReduce<P, Q, F>
where
    I: Input,
    N: Reborrow,
    L: RbBack,
    E: ErrorSink<I::Pos>,
    P: Parser<I, N, L, E>,
    Q: Parser<I, N, L, E, Out = Op>,
    F: Fn(P::Out, Op, P::Out) -> P::Out,
{
    #[inline]
    fn parse(&self, mut input: In<I, N, L, E>) -> Option<P::Out> {
        let mut left = self.0.parse(input.rb())?;
        loop {
            match input.maybe(self.1.by_ref()) {
                Some(Some(op_value)) => {
                    let right = self.0.parse(input.rb())?;
                    left = (self.2)(left, op_value, right);
                }
                Some(None) => return Some(left),
                None => return None,
            }
        }
    }
}

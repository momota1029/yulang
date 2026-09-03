//! Input, recoverable state, and the handle passed to a parser procedure.

use reborrow_generic::{Reborrow, short::Rb};

use crate::parser::ParserOnce;

/// A cursor-based input stream.
///
/// `Index` is an opaque, cheap cursor identity used by the direct function
/// parser implementation to verify the `None` contract. Equality must mean
/// that two indices identify the same reachable cursor position during one
/// transaction. It is not a source range, a comparison of input text, or a
/// comparison of recoverable state.
pub trait Input {
    type Item;
    type Mark;
    type Index: Eq;

    fn next(&mut self) -> Option<Self::Item>;
    fn mark(&self) -> Self::Mark;
    fn rollback(&mut self, mark: Self::Mark);
    fn index(&self) -> Self::Index;
}

impl<'source> Input for &'source str {
    type Item = char;
    type Mark = &'source str;
    type Index = *const u8;

    fn next(&mut self) -> Option<Self::Item> {
        let mut chars = self.chars();
        let item = chars.next()?;
        *self = chars.as_str();
        Some(item)
    }

    fn mark(&self) -> Self::Mark {
        *self
    }

    fn rollback(&mut self, mark: Self::Mark) {
        *self = mark;
    }

    fn index(&self) -> Self::Index {
        self.as_ptr()
    }
}

/// A concrete state whose mutations can be rolled back on non-match.
///
/// The marker is a passive snapshot: taking one holds no borrow or active
/// resource, nested marks remain valid, and success commits by dropping it.
pub trait Recoverable {
    type Mark;

    fn mark(&self) -> Self::Mark;
    fn rollback(&mut self, mark: Self::Mark);
}

/// A reborrowable recover-state capability.
///
/// This static form lets [`In`] store `R::Target<'a>` and create short parser
/// calls without retaining a long `&mut R`. The direct unit-state function
/// [`ParserOnce`] implementation rolls it back on `None` but never compares it
/// for equality.
pub trait Recover: Rb {
    type Mark;

    fn mark<'a>(this: Self::Target<'a>) -> Self::Mark;
    fn rollback<'a>(this: Self::Target<'a>, mark: Self::Mark);
}

impl<'state, T: Recoverable + ?Sized> Recover for &'state mut T {
    type Mark = T::Mark;

    fn mark<'a>(this: &'a mut T) -> Self::Mark {
        Recoverable::mark(this)
    }

    fn rollback<'a>(this: &'a mut T, mark: Self::Mark) {
        Recoverable::rollback(this, mark);
    }
}

impl Recover for () {
    type Mark = ();

    fn mark<'a>(_: ()) -> Self::Mark {}

    fn rollback<'a>(_: (), _: Self::Mark) {}
}

/// The capabilities passed to one parser invocation.
///
/// Grammar parsers use `S = ()`. [`In::then`] hands its total callback an
/// arbitrary reborrowable `S`. The lexical [`In::token`] and optional
/// [`In::maybe`] conveniences privately use a short unit-state reborrow, so
/// their parsers cannot observe or mutate the outer `S`.
#[derive(Reborrow)]
pub struct In<'a, I: Input, R: Recover + 'a = (), S: Rb + 'a = ()> {
    pub(crate) input: &'a mut I,
    pub(crate) recovery: R::Target<'a>,
    /// Non-recoverable state supplied to [`In::then`] or `ParserOnce::then`.
    pub state: S::Target<'a>,
}

impl<'a, I: Input, R: Recover + 'a, S: Rb + 'a> In<'a, I, R, S> {
    /// Construct an input from the targets of the recover and simple states.
    pub fn new(input: &'a mut I, recovery: R::Target<'a>, state: S::Target<'a>) -> Self {
        Self {
            input,
            recovery,
            state,
        }
    }

    /// Return the input's opaque cursor identity.
    pub fn index(&self) -> I::Index {
        self.input.index()
    }

    /// Run one lexical transaction through a short unit-state reborrow.
    ///
    /// The raw procedure cannot observe or mutate `S`. Unlike an ordinary
    /// function parser, it may consume before returning `None`; [`token`]
    /// restores both input and recoverable state in that case.
    pub fn token<F, O>(&mut self, token: F) -> Option<O>
    where
        F: for<'short> FnOnce(In<'short, I, R, ()>) -> Option<O>,
    {
        let grammar = In::<I, R, ()>::new(&mut *self.input, R::shorten_mut(&mut self.recovery), ());
        crate::parser::token(token).run_once(grammar)
    }

    /// Run an optional unit-state parser through a short reborrow.
    ///
    /// Parser absence is represented by the inner `None`; the outer `Option`
    /// is always `Some` because [`maybe`] itself always succeeds.
    pub fn maybe<P>(&mut self, parser: P) -> Option<Option<P::Output>>
    where
        P: ParserOnce<I, R, ()>,
    {
        let grammar = In::<I, R, ()>::new(&mut *self.input, R::shorten_mut(&mut self.recovery), ());
        crate::parser::maybe(parser).run_once(grammar)
    }

    /// Run a unit-state parser and map its successful output.
    ///
    /// The mapping receives only the parser output. A private unit-state
    /// bridge runs it through [`In::check`]. A direct unit-state function
    /// parser rolls recoverable state back on `None` and verifies its own
    /// input-nonconsumption contract.
    pub fn map<P, F, O2>(self, parser: P, map: F) -> Option<O2>
    where
        P: ParserOnce<I, R, ()>,
        F: FnOnce(P::Output) -> O2,
    {
        self.then(parser, |output, _| map(output))
    }

    /// Run a unit-state parser, then hand its output and this owned input to a
    /// total procedural continuation.
    ///
    /// This is the central state-lifting primitive. A private unit-state bridge
    /// runs the parser through [`In::check`]. The continuation runs only after
    /// success and returns an ordinary output directly; it cannot make this
    /// method backtrack.
    pub fn then<P, F, O2>(mut self, parser: P, then: F) -> Option<O2>
    where
        P: ParserOnce<I, R, ()>,
        F: FnOnce(P::Output, Self) -> O2,
    {
        let output = {
            let mut grammar =
                In::<I, R, ()>::new(&mut *self.input, R::shorten_mut(&mut self.recovery), ());
            grammar.check(parser)?
        };
        Some(then(output, self))
    }
}

impl<'a, 'source, R: Recover + 'a, S: Rb + 'a> In<'a, &'source str, R, S> {
    /// Run an operation through a short reborrow and return the exact source
    /// prefix it consumed from the current cursor.
    ///
    /// This is source capture, not lookahead: it neither reads input itself nor
    /// stores a future item. The nested operation owns its ordinary success,
    /// non-match, and rollback behavior. In particular, this method never
    /// corrects the input cursor. The `In` handle is consumed as a one-shot
    /// continuation boundary; call `i.rb().with_str(...)` when the caller must
    /// retain and reuse its outer handle.
    pub fn with_str<O, F>(mut self, operation: F) -> (O, &'source str)
    where
        F: for<'short> FnOnce(In<'short, &'source str, R, S>) -> O,
    {
        let start = *self.input;
        let output = operation(self.rb());
        let end = *self.input;

        let consumed_len = start
            .len()
            .checked_sub(end.len())
            .expect("with_str operation replaced the input with a longer suffix");
        assert_eq!(
            start.as_ptr().wrapping_add(consumed_len),
            end.as_ptr(),
            "with_str operation replaced the input with an unrelated slice"
        );

        (output, &start[..consumed_len])
    }
}

impl<I: Input, R: Recover> In<'_, I, R, ()> {
    /// Consume one item. A procedure that later returns `None` must restore
    /// this consumption itself; the direct unit-state function [`ParserOnce`]
    /// impl diagnoses violations.
    pub fn next(&mut self) -> Option<I::Item> {
        self.input.next()
    }

    /// Reborrow the recoverable parser-local state for immediate use.
    pub fn recovery(&mut self) -> R::Target<'_> {
        R::shorten_mut(&mut self.recovery)
    }

    /// Run a unit-state grammar parser.
    ///
    /// This preserves the readable `i.check(parser)?` grammar spelling. The
    /// parser itself owns its transaction: the direct unit-state function
    /// [`ParserOnce`] implementation rolls recoverable state back on `None`
    /// and checks [`Input::Index`], while tuple and choice parsers restore
    /// their own composite transactions. No input mark or input correction
    /// occurs here.
    pub fn check<P>(&mut self, parser: P) -> Option<P::Output>
    where
        P: ParserOnce<I, R, ()>,
    {
        parser.run_once(self.rb())
    }

    pub(crate) fn checkpoint(&mut self) -> Checkpoint<I::Mark, R::Mark> {
        Checkpoint {
            input: self.input.mark(),
            recovery: R::mark(R::shorten_mut(&mut self.recovery)),
        }
    }

    pub(crate) fn rollback(&mut self, checkpoint: Checkpoint<I::Mark, R::Mark>) {
        self.input.rollback(checkpoint.input);
        R::rollback(R::shorten_mut(&mut self.recovery), checkpoint.recovery);
    }

    pub(crate) fn input_mark(&self) -> I::Mark {
        self.input.mark()
    }

    pub(crate) fn input_rollback(&mut self, mark: I::Mark) {
        self.input.rollback(mark);
    }
}

pub(crate) struct Checkpoint<I, R> {
    input: I,
    recovery: R,
}

//! The one-pass grammar trait and its deliberately small composition surface.

use reborrow_generic::short::Rb;

use crate::input::{In, Input, Recover};

/// A parser that either non-matches without changing input or recoverable
/// state, or returns a normal value (including a value representing recovered
/// syntax). `S` is non-recoverable: a non-unit-state implementation must be
/// total, or leave `S` unchanged when it returns `None`.
pub trait ParserOnce<I: Input, R: Recover, S: Rb> {
    type Output;

    fn run_once(self, input: In<'_, I, R, S>) -> Option<Self::Output>;

    /// Map one successful output with an owned closure.
    fn map_once<O2, F>(self, map: F) -> MapOnce<Self, F>
    where
        Self: Sized,
        F: FnOnce(Self::Output) -> O2,
    {
        MapOnce { parser: self, map }
    }

    /// Map one successful output with a mutable closure.
    fn map_mut<O2, F>(self, map: F) -> MapMut<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Output) -> O2,
    {
        MapMut { parser: self, map }
    }

    /// Map one successful output with a shared closure.
    fn map<O2, F>(self, map: F) -> Map<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Output) -> O2,
    {
        Map { parser: self, map }
    }

    /// Lift a successful unit-state grammar parser into non-recoverable state.
    ///
    /// The callback has the exact shape `FnOnce(O1, In<I, R, S2>) -> O2` and
    /// is intentionally total. Its implementation privately bridges through a
    /// unit-state input before handing the callback the original `S2`. With
    /// `S2 = ()`, it is a committed procedural escape hatch: it may consume
    /// input, but its direct output cannot propagate `None` through `then`.
    /// There is no `bind`, `flat_map`, or `and_then`.
    fn then<S2, O2, F>(self, map: F) -> Then<Self, F>
    where
        Self: Sized + ParserOnce<I, R, ()>,
        S2: Rb,
        F: for<'a> FnOnce(<Self as ParserOnce<I, R, ()>>::Output, In<'a, I, R, S2>) -> O2,
    {
        Then { parser: self, map }
    }
}

/// Construction methods whose input type is fixed by the returned parser.
///
/// This separate extension trait keeps `.with_str()` inferable: the generic
/// `I`, `R`, and `S` parameters of [`ParserOnce`] are not known until the
/// returned parser is run.
pub trait ParserOnceStrExt: Sized {
    /// Capture the exact `&str` source interval consumed on success.
    ///
    /// Capture does not read ahead or add a transaction. On non-match, the
    /// wrapped parser remains solely responsible for preserving input and
    /// recoverable state according to its existing contract.
    fn with_str(self) -> WithStr<Self> {
        WithStr { parser: self }
    }
}

impl<P> ParserOnceStrExt for P {}

/// A parser paired with the exact borrowed `&str` interval it consumes.
#[must_use]
pub struct WithStr<P> {
    parser: P,
}

impl<'source, R, S, P, O> ParserOnce<&'source str, R, S> for WithStr<P>
where
    R: Recover,
    S: Rb,
    P: ParserOnce<&'source str, R, S, Output = O>,
{
    type Output = (O, &'source str);

    fn run_once(self, input: In<'_, &'source str, R, S>) -> Option<Self::Output> {
        let (output, consumed) = input.with_str(|input| self.parser.run_once(input));
        output.map(|output| (output, consumed))
    }
}

impl<I: Input, R: Recover, F, O> ParserOnce<I, R, ()> for F
where
    F: for<'a> FnOnce(In<'a, I, R, ()>) -> Option<O>,
{
    type Output = O;

    fn run_once(self, mut input: In<'_, I, R, ()>) -> Option<Self::Output> {
        let index = input.index();
        let recovery_mark = R::mark(R::shorten_mut(&mut input.recovery));
        let output = self(input.rb());

        if output.is_none() {
            R::rollback(R::shorten_mut(&mut input.recovery), recovery_mark);
            if input.index() != index {
                panic!(
                    "ParserOnce function returned None after consuming input; None must preserve Input::Index"
                );
            }
        }

        output
    }
}

/// A raw lexical procedure with input and recover-state rollback on non-match.
#[must_use]
pub struct Token<F>(F);

/// Construct the one explicitly transactional lexical parser.
///
/// The procedure is invoked directly, outside the ordinary function
/// [`ParserOnce`] boundary. It receives only unit state and may consume before
/// returning `None`; [`Token`] then restores both input and recoverable state.
pub fn token<F>(token: F) -> Token<F> {
    Token(token)
}

impl<I, R, F, O> ParserOnce<I, R, ()> for Token<F>
where
    I: Input,
    R: Recover,
    F: for<'short> FnOnce(In<'short, I, R, ()>) -> Option<O>,
{
    type Output = O;

    fn run_once(self, mut input: In<'_, I, R, ()>) -> Option<Self::Output> {
        let checkpoint = input.checkpoint();
        let output = (self.0)(input.rb());
        if output.is_none() {
            input.rollback(checkpoint);
        }
        output
    }
}

/// An optional unit-state parser whose own invocation always succeeds.
#[must_use]
pub struct Maybe<P>(P);

/// Turn parser non-match into a successful optional value.
///
/// This adds no transaction. The inner parser remains responsible for its
/// own non-match contract.
pub fn maybe<P>(parser: P) -> Maybe<P> {
    Maybe(parser)
}

impl<I, R, P> ParserOnce<I, R, ()> for Maybe<P>
where
    I: Input,
    R: Recover,
    P: ParserOnce<I, R, ()>,
{
    type Output = Option<P::Output>;

    fn run_once(self, mut input: In<'_, I, R, ()>) -> Option<Self::Output> {
        Some(input.check(self.0))
    }
}

/// An owned output mapping after a successful parser.
#[must_use]
pub struct MapOnce<P, F> {
    parser: P,
    map: F,
}

impl<I, R, S, P, F, O1, O2> ParserOnce<I, R, S> for MapOnce<P, F>
where
    I: Input,
    R: Recover,
    S: Rb,
    P: ParserOnce<I, R, S, Output = O1>,
    F: FnOnce(O1) -> O2,
{
    type Output = O2;

    fn run_once(self, input: In<'_, I, R, S>) -> Option<Self::Output> {
        self.parser.run_once(input).map(self.map)
    }
}

/// A mutable output mapping after a successful parser.
#[must_use]
pub struct MapMut<P, F> {
    parser: P,
    map: F,
}

impl<I, R, S, P, F, O1, O2> ParserOnce<I, R, S> for MapMut<P, F>
where
    I: Input,
    R: Recover,
    S: Rb,
    P: ParserOnce<I, R, S, Output = O1>,
    F: FnMut(O1) -> O2,
{
    type Output = O2;

    fn run_once(self, input: In<'_, I, R, S>) -> Option<Self::Output> {
        let Self { parser, mut map } = self;
        parser.run_once(input).map(&mut map)
    }
}

/// A shared output mapping after a successful parser.
#[must_use]
pub struct Map<P, F> {
    parser: P,
    map: F,
}

impl<I, R, S, P, F, O1, O2> ParserOnce<I, R, S> for Map<P, F>
where
    I: Input,
    R: Recover,
    S: Rb,
    P: ParserOnce<I, R, S, Output = O1>,
    F: Fn(O1) -> O2,
{
    type Output = O2;

    fn run_once(self, input: In<'_, I, R, S>) -> Option<Self::Output> {
        self.parser.run_once(input).map(self.map)
    }
}

/// A committed total phase after a successful unit-state grammar parser.
#[must_use]
pub struct Then<P, F> {
    parser: P,
    map: F,
}

impl<I, R, S, P, F, O1, O2> ParserOnce<I, R, S> for Then<P, F>
where
    I: Input,
    R: Recover,
    S: Rb,
    P: ParserOnce<I, R, (), Output = O1>,
    F: for<'a> FnOnce(O1, In<'a, I, R, S>) -> O2,
{
    type Output = O2;

    fn run_once(self, input: In<'_, I, R, S>) -> Option<Self::Output> {
        input.then(self.parser, self.map)
    }
}

impl<I: Input, R: Recover> ParserOnce<I, R, ()> for () {
    type Output = ();

    fn run_once(self, _: In<'_, I, R, ()>) -> Option<Self::Output> {
        Some(())
    }
}

macro_rules! tuple_parser {
    ($(($P:ident, $p:ident)),+ $(,)?) => {
        impl<I, R, $($P),+> ParserOnce<I, R, ()> for ($($P,)+)
        where
            I: Input,
            R: Recover,
            $($P: ParserOnce<I, R, ()>,)+
        {
            type Output = ($($P::Output,)+);

            fn run_once(self, mut input: In<'_, I, R, ()>) -> Option<Self::Output> {
                let checkpoint = input.checkpoint();
                let ($($p,)+) = self;
                let output = (|| {
                    $(let $p = input.check($p)?;)+
                    Some(($($p,)+))
                })();

                if output.is_none() {
                    input.rollback(checkpoint);
                }
                output
            }
        }
    };
}

tuple_parser!((P0, p0));
tuple_parser!((P0, p0), (P1, p1));
tuple_parser!((P0, p0), (P1, p1), (P2, p2));
tuple_parser!((P0, p0), (P1, p1), (P2, p2), (P3, p3));
tuple_parser!((P0, p0), (P1, p1), (P2, p2), (P3, p3), (P4, p4));
tuple_parser!((P0, p0), (P1, p1), (P2, p2), (P3, p3), (P4, p4), (P5, p5));
tuple_parser!(
    (P0, p0),
    (P1, p1),
    (P2, p2),
    (P3, p3),
    (P4, p4),
    (P5, p5),
    (P6, p6)
);

/// A set of unit-state alternatives tried from left to right.
#[must_use]
pub struct Choice<P>(P);

/// Try unit-state parsers from left to right until one succeeds.
///
/// Every alternative runs through [`In::check`]. If all alternatives
/// non-match, the outer input and recover-state checkpoint is restored.
pub fn choice<P>(parsers: P) -> Choice<P> {
    Choice(parsers)
}

macro_rules! choice_parser {
    ($(($P:ident, $p:ident)),+ $(,)?) => {
        impl<I, R, O, $($P),+> ParserOnce<I, R, ()> for Choice<($($P,)+)>
        where
            I: Input,
            R: Recover,
            $($P: ParserOnce<I, R, (), Output = O>,)+
        {
            type Output = O;

            fn run_once(self, mut input: In<'_, I, R, ()>) -> Option<Self::Output> {
                let checkpoint = input.checkpoint();
                let Choice(($($p,)+)) = self;

                $(if let Some(output) = input.check($p) {
                    return Some(output);
                })+

                input.rollback(checkpoint);
                None
            }
        }
    };
}

choice_parser!((P0, p0));
choice_parser!((P0, p0), (P1, p1));
choice_parser!((P0, p0), (P1, p1), (P2, p2));
choice_parser!((P0, p0), (P1, p1), (P2, p2), (P3, p3));
choice_parser!((P0, p0), (P1, p1), (P2, p2), (P3, p3), (P4, p4));
choice_parser!((P0, p0), (P1, p1), (P2, p2), (P3, p3), (P4, p4), (P5, p5));
choice_parser!(
    (P0, p0),
    (P1, p1),
    (P2, p2),
    (P3, p3),
    (P4, p4),
    (P5, p5),
    (P6, p6)
);
choice_parser!(
    (P0, p0),
    (P1, p1),
    (P2, p2),
    (P3, p3),
    (P4, p4),
    (P5, p5),
    (P6, p6),
    (P7, p7)
);
tuple_parser!(
    (P0, p0),
    (P1, p1),
    (P2, p2),
    (P3, p3),
    (P4, p4),
    (P5, p5),
    (P6, p6),
    (P7, p7)
);

/// Match and consume one item equal to `expected`.
#[must_use]
pub struct Item<T>(T);

/// Construct an [`Item`] parser.
pub fn item<T>(expected: T) -> Item<T> {
    Item(expected)
}

impl<I, R, T> ParserOnce<I, R, ()> for Item<T>
where
    I: Input,
    R: Recover,
    T: PartialEq<I::Item>,
{
    type Output = I::Item;

    fn run_once(self, mut input: In<'_, I, R, ()>) -> Option<Self::Output> {
        let mark = input.input_mark();
        match input.next() {
            Some(item) if self.0.eq(&item) => Some(item),
            Some(_) | None => {
                input.input_rollback(mark);
                None
            }
        }
    }
}

/// Match end-of-input without consuming it.
pub fn eoi<I, R>() -> impl ParserOnce<I, R, (), Output = ()>
where
    I: Input,
    R: Recover,
{
    |mut input: In<'_, I, R, ()>| {
        let mark = input.input_mark();
        let at_end = input.next().is_none();
        input.input_rollback(mark);
        at_end.then_some(())
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use reborrow_generic::Reborrow as _;

    use super::{ParserOnce, ParserOnceStrExt, choice, item, maybe, token};
    use crate::input::{In, Recoverable};

    #[derive(Default)]
    struct Log(Vec<char>);

    impl Recoverable for Log {
        type Mark = usize;

        fn mark(&self) -> Self::Mark {
            self.0.len()
        }

        fn rollback(&mut self, mark: Self::Mark) {
            self.0.truncate(mark);
        }
    }

    #[derive(Default)]
    struct CountingInput {
        mark_calls: Cell<usize>,
        index_calls: Cell<usize>,
        rollback_calls: usize,
    }

    impl crate::input::Input for CountingInput {
        type Item = ();
        type Mark = ();
        type Index = ();

        fn next(&mut self) -> Option<Self::Item> {
            None
        }

        fn mark(&self) -> Self::Mark {
            self.mark_calls.set(self.mark_calls.get() + 1);
        }

        fn rollback(&mut self, _: Self::Mark) {
            self.rollback_calls += 1;
        }

        fn index(&self) -> Self::Index {
            self.index_calls.set(self.index_calls.get() + 1);
        }
    }

    #[derive(Default)]
    struct CountingRecovery {
        mark_calls: Cell<usize>,
        rollback_calls: usize,
    }

    impl Recoverable for CountingRecovery {
        type Mark = ();

        fn mark(&self) -> Self::Mark {
            self.mark_calls.set(self.mark_calls.get() + 1);
        }

        fn rollback(&mut self, _: Self::Mark) {
            self.rollback_calls += 1;
        }
    }

    struct TrustedNonMatch;

    impl ParserOnce<CountingInput, &mut CountingRecovery, ()> for TrustedNonMatch {
        type Output = ();

        fn run_once(
            self,
            _: In<'_, CountingInput, &mut CountingRecovery, ()>,
        ) -> Option<Self::Output> {
            None
        }
    }

    #[test]
    fn in_reborrows_recover_and_sink_targets() {
        fn write_once(input: In<&str, &mut Log, &mut String>) {
            input.recovery.0.push('r');
            input.state.push('s');
        }

        let mut source = "";
        let mut log = Log::default();
        let mut sink = String::new();
        let mut input = In::<_, &mut Log, &mut String>::new(&mut source, &mut log, &mut sink);
        write_once(input.rb());
        write_once(input.rb());

        assert_eq!(log.0, ['r', 'r']);
        assert_eq!(sink, "ss");
    }

    #[test]
    fn tuple_non_match_restores_input_and_recoverable_state() {
        let mut source = "ab";
        let mut log = Log::default();
        let parser = (
            |mut input: In<&str, &mut Log, ()>| {
                input.recovery().0.push('x');
                input.next();
                Some(())
            },
            item('z'),
        );

        assert_eq!(
            parser.run_once(In::<_, &mut Log, ()>::new(&mut source, &mut log, ())),
            None
        );
        assert_eq!(source, "ab");
        assert!(log.0.is_empty());
    }

    #[test]
    fn choice_rolls_back_failed_alternatives_and_all_none_scope() {
        let mut source = "a!";
        let mut log = Log::default();
        let first = |mut input: In<&str, &mut Log, ()>| {
            input.recovery().0.push('x');
            None::<char>
        };
        let parser = choice((first, item('a')));

        assert_eq!(
            parser.run_once(In::<_, &mut Log, ()>::new(&mut source, &mut log, ())),
            Some('a')
        );
        assert_eq!(source, "!");
        assert!(log.0.is_empty());

        let mut source = "a!";
        let first = |mut input: In<&str, &mut Log, ()>| {
            input.recovery().0.push('y');
            None::<char>
        };
        let parser = choice((first, item('z')));

        assert_eq!(
            parser.run_once(In::<_, &mut Log, ()>::new(&mut source, &mut log, ())),
            None
        );
        assert_eq!(source, "a!");
        assert!(log.0.is_empty());
    }

    #[test]
    #[should_panic(expected = "None after consuming input")]
    fn function_parser_rejects_a_consume_then_none_procedure_by_cursor_identity() {
        let mut source = "a";
        let recovery = ();

        let _ = (|mut nested: In<&str, (), ()>| {
            nested.next();
            None::<()>
        })
        .run_once(In::<_, (), ()>::new(&mut source, recovery, ()));
    }

    #[test]
    fn then_rolls_back_recovery_but_does_not_correct_a_contract_violation() {
        use std::panic::{AssertUnwindSafe, catch_unwind};

        let mut source = "a";
        let mut log = Log::default();
        let mut sink = String::new();
        let grammar = |mut input: In<&str, &mut Log, ()>| {
            input.recovery().0.push('x');
            input.next();
            None::<()>
        };
        let parser =
            grammar.then(|(), input: In<&str, &mut Log, &mut String>| input.state.push('!'));

        let result = catch_unwind(AssertUnwindSafe(|| {
            parser.run_once(In::<_, &mut Log, &mut String>::new(
                &mut source,
                &mut log,
                &mut sink,
            ))
        }));

        assert!(result.is_err());
        assert_eq!(source, "");
        assert!(log.0.is_empty());
        assert!(sink.is_empty());
    }

    #[test]
    fn function_parser_rolls_back_recoverable_state_without_comparing_it() {
        let mut source = "a";
        let mut log = Log::default();

        let output = (|mut nested: In<&str, &mut Log, ()>| {
            nested.recovery().0.push('x');
            None::<()>
        })
        .run_once(In::<_, &mut Log, ()>::new(&mut source, &mut log, ()));

        assert_eq!(output, None);
        assert_eq!(source, "a");
        assert!(log.0.is_empty());
    }

    #[test]
    fn token_non_match_restores_utf8_input_and_recoverable_state() {
        let mut source = "β!";
        let mut log = Log::default();
        let parser = token(|mut input: In<&str, &mut Log, ()>| {
            input.recovery().0.push('x');
            assert_eq!(input.next(), Some('β'));
            None::<char>
        });

        assert_eq!(
            parser.run_once(In::<_, &mut Log, ()>::new(&mut source, &mut log, ())),
            None
        );
        assert_eq!(source, "β!");
        assert!(log.0.is_empty());
    }

    #[test]
    fn token_success_commits_input_and_recoverable_state() {
        let mut source = "β!";
        let mut log = Log::default();
        let parser = token(|mut input: In<&str, &mut Log, ()>| {
            input.recovery().0.push('x');
            input.next()
        });

        assert_eq!(
            parser.run_once(In::<_, &mut Log, ()>::new(&mut source, &mut log, ())),
            Some('β')
        );
        assert_eq!(source, "!");
        assert_eq!(log.0, ['x']);
    }

    #[test]
    fn maybe_token_preserves_nested_match_and_absence_shapes() {
        let mut matched_source = "ab";
        let mut matched_log = Log::default();
        let matched = maybe(token(|mut input: In<&str, &mut Log, ()>| {
            input.recovery().0.push('x');
            input.next()
        }));

        assert_eq!(
            matched.run_once(In::<_, &mut Log, ()>::new(
                &mut matched_source,
                &mut matched_log,
                (),
            )),
            Some(Some('a'))
        );
        assert_eq!(matched_source, "b");
        assert_eq!(matched_log.0, ['x']);

        let mut absent_source = "β!";
        let mut absent_log = Log::default();
        let absent = maybe(token(|mut input: In<&str, &mut Log, ()>| {
            input.recovery().0.push('y');
            input.next();
            None::<char>
        }));

        assert_eq!(
            absent.run_once(In::<_, &mut Log, ()>::new(
                &mut absent_source,
                &mut absent_log,
                (),
            )),
            Some(None)
        );
        assert_eq!(absent_source, "β!");
        assert!(absent_log.0.is_empty());
    }

    #[test]
    fn in_token_and_maybe_hide_outer_simple_state() {
        let mut source = "a!";
        let mut log = Log::default();
        let mut sink = String::from("opaque");
        let mut input = In::<_, &mut Log, &mut String>::new(&mut source, &mut log, &mut sink);

        let token_output = input.token(|mut token: In<&str, &mut Log, ()>| {
            token.recovery().0.push('x');
            token.next()
        });
        let maybe_output = input.maybe(token(|mut token: In<&str, &mut Log, ()>| {
            token.recovery().0.push('y');
            token.next();
            None::<char>
        }));

        assert_eq!(token_output, Some('a'));
        assert_eq!(maybe_output, Some(None));
        assert_eq!(source, "!");
        assert_eq!(log.0, ['x']);
        assert_eq!(sink, "opaque");
    }

    #[test]
    fn check_delegates_without_its_own_input_or_recovery_transaction() {
        let mut source = CountingInput::default();
        let mut recovery = CountingRecovery::default();

        {
            let mut input = In::<_, &mut CountingRecovery, ()>::new(&mut source, &mut recovery, ());
            assert_eq!(input.check(TrustedNonMatch), None);
        }

        assert_eq!(source.mark_calls.get(), 0);
        assert_eq!(source.index_calls.get(), 0);
        assert_eq!(source.rollback_calls, 0);
        assert_eq!(recovery.mark_calls.get(), 0);
        assert_eq!(recovery.rollback_calls, 0);
    }

    #[test]
    fn in_map_and_then_keep_output_and_procedural_capabilities_distinct() {
        let mut source = "ab!";
        let output = In::<_, (), ()>::new(&mut source, (), ())
            .map((item('a'), item('b')), |(a, b)| String::from_iter([a, b]));

        assert_eq!(output, Some(String::from("ab")));
        assert_eq!(source, "!");

        let mut source = "ab!";
        let recovery = ();
        let mut sink = String::new();
        let input = In::<_, (), &mut String>::new(&mut source, recovery, &mut sink);

        let output = input.then((item('a'), item('b')), |(a, b), input| {
            input.state.push(a);
            input.state.push(b);
            input.index()
        });

        assert_eq!(output, Some(source.as_ptr()));
        assert_eq!(sink, "ab");
        assert_eq!(source, "!");
    }

    #[test]
    fn then_does_not_run_when_grammar_non_matches() {
        let mut source = "az";
        let recovery = ();
        let mut sink = String::new();
        let parser = (item('a'), item('b'))
            .then(|_, input: In<&str, (), &mut String>| input.state.push('!'));

        assert_eq!(
            parser.run_once(In::<_, (), &mut String>::new(
                &mut source,
                recovery,
                &mut sink,
            )),
            None
        );
        assert_eq!(source, "az");
        assert!(sink.is_empty());
    }

    #[test]
    fn ordinary_map_variants_transform_only_parser_output() {
        fn take_a(input: In<&str, (), ()>) -> Option<char> {
            item('a').run_once(input)
        }

        let mut source = "abc";
        let mut calls = 0;
        let parser = take_a
            .map_once(|item: char| item.to_ascii_uppercase())
            .map_mut(|item: char| {
                calls += 1;
                (item, calls)
            })
            .map(|(item, calls)| format!("{item}{calls}"));

        assert_eq!(
            parser.run_once(In::<_, (), ()>::new(&mut source, (), ())),
            Some(String::from("A1"))
        );
        assert_eq!(source, "bc");
        assert_eq!(calls, 1);
    }

    #[test]
    fn in_with_str_supports_nested_current_cursor_capture() {
        let mut source = "aβ!";
        let input = In::<_, (), ()>::new(&mut source, (), ());

        let ((first, second, inner), outer) = input.with_str(|mut outer| {
            let first = outer.next().unwrap();
            let (second, inner) = outer.rb().with_str(|mut inner| inner.next().unwrap());
            (first, second, inner)
        });

        assert_eq!((first, second), ('a', 'β'));
        assert_eq!(inner, "β");
        assert_eq!(outer, "aβ");
        assert_eq!(source, "!");
    }

    #[test]
    fn in_with_str_captures_utf8_crlf_and_zero_consumption_without_copying() {
        let original = "界\r\nrest";
        let mut source = original;
        let mut input = In::<_, (), ()>::new(&mut source, (), ());

        let ((), empty) = input.rb().with_str(|_| ());
        let (items, consumed) = input.with_str(|mut nested| {
            [
                nested.next().unwrap(),
                nested.next().unwrap(),
                nested.next().unwrap(),
            ]
        });

        assert_eq!(empty, "");
        assert_eq!(empty.as_ptr(), original.as_ptr());
        assert_eq!(items, ['界', '\r', '\n']);
        assert_eq!(consumed, "界\r\n");
        assert_eq!(consumed.as_ptr(), original.as_ptr());
        assert_eq!(source, "rest");
    }

    #[test]
    fn parser_with_str_returns_successful_output_and_exact_source() {
        let mut source = "aβ!";
        let parser = (item('a'), item('β')).with_str();

        assert_eq!(
            parser.run_once(In::<_, (), ()>::new(&mut source, (), ())),
            Some((('a', 'β'), "aβ"))
        );
        assert_eq!(source, "!");
    }

    #[test]
    fn parser_with_str_preserves_non_match_input_and_recovery_rollback() {
        let mut source = "ab";
        let mut log = Log::default();
        let parser = (
            |mut input: In<&str, &mut Log, ()>| {
                input.recovery().0.push('x');
                input.next();
                Some(())
            },
            item('z'),
        )
            .with_str();

        assert_eq!(
            parser.run_once(In::<_, &mut Log, ()>::new(&mut source, &mut log, ())),
            None
        );
        assert_eq!(source, "ab");
        assert!(log.0.is_empty());
    }

    #[test]
    fn parser_with_str_preserves_non_recoverable_state_capability() {
        let mut source = "a!";
        let mut sink = String::new();
        let parser = item('a')
            .then(|item, input: In<&str, (), &mut String>| input.state.push(item))
            .with_str();

        assert_eq!(
            parser.run_once(In::<_, (), &mut String>::new(&mut source, (), &mut sink,)),
            Some(((), "a"))
        );
        assert_eq!(source, "!");
        assert_eq!(sink, "a");
    }
}

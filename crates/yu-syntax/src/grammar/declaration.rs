//! Shared grammar for source-leading declarations.

use std::ops::Range;

use chasa::{
    Back as _, ErrorSink, Input as _,
    error::std::{Unexpected, UnexpectedEndOfInput},
    parser::Parser as _,
    prelude::from_fn,
};

use crate::{
    BindingPower as HeaderBindingPower, BindingPowers, HeaderImport, HeaderImportForm,
    HeaderImportRoute, HeaderImportRouteSeparator, HeaderOperator, Visibility,
    grammar::expression::{Expression, ParsedExpression, parse_direct_expression_with_operators, parse_expression},
    operator::{BindingPower, OperatorFixity},
    scan::{
        operator::LeadingTrivia,
        punctuation::{PunctuationKind, scan_punctuation},
        trivia::{TriviaRun, scan_trivia},
        word::{WordSpan, scan_word},
    },
    session::{CommitOutput, Committed, Delimiter, Probe, SynIn},
    syntax_kind::SyntaxKind,
};

/// One parsed source-leading declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Declaration<'source> {
    Use(UseDeclaration<'source>),
    Binding(BindingDeclaration<'source>),
    OperatorHeader(OperatorHeaderDeclaration<'source>),
}

/// A declaration shape that can contribute a source-leading header fact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum HeaderDeclaration<'source> {
    Use(UseDeclaration<'source>),
    OperatorHeader(OperatorHeaderDeclaration<'source>),
}

/// The sink-free declaration prefix that selects a direct-CST continuation.
///
/// Recognition owns all contextual-keyword classification and leading inline
/// trivia. The accepted continuation emits these already-scanned ranges only
/// after [`commit_header_statement`] has transferred the input to
/// [`Committed`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum HeaderStatementIntro<'source> {
    Use(UseStatementIntro<'source>),
    Operator(OperatorStatementIntro<'source>),
}

/// The shared root-statement classification before header mode excludes
/// binding declarations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum StatementIntro<'source> {
    Use(UseStatementIntro<'source>),
    Binding(BindingStatementIntro<'source>),
    Operator(OperatorStatementIntro<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UseStatementIntro<'source> {
    start: usize,
    visibility: Option<VisibilityPrefix<'source>>,
    after_visibility: Option<TriviaRun>,
    use_keyword: WordSpan<'source>,
    after_use: TriviaRun,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OperatorStatementIntro<'source> {
    start: usize,
    visibility: Option<VisibilityPrefix<'source>>,
    lazy_keyword: Option<WordSpan<'source>>,
    after_visibility: Option<TriviaRun>,
    after_lazy: Option<TriviaRun>,
    fixity_keyword: WordSpan<'source>,
    after_fixity: TriviaRun,
    fixity: OperatorFixity,
}

/// The committed prefix of a direct binding declaration.
///
/// The continuation owns the mandatory name, equals, and value slots; keeping
/// them out of this sink-free prefix is what lets the root statement loop cut
/// at `my` before recovery is selected.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BindingStatementIntro<'source> {
    start: usize,
    my_keyword: WordSpan<'source>,
}

pub(crate) struct ParsedBindingDeclaration<'source, C> {
    range: Range<usize>,
    name: WordSpan<'source>,
    value: ParsedExpression<C>,
}

impl<'source, C> ParsedBindingDeclaration<'source, C> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn name(&self) -> WordSpan<'source> {
        self.name
    }

    pub(crate) fn value(&self) -> &ParsedExpression<C> {
        &self.value
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct VisibilityPrefix<'source> {
    visibility: Visibility,
    keyword: WordSpan<'source>,
}

/// Recognizes one source-leading header declaration and transfers it to a
/// direct-emission continuation.
///
/// A failed recognition rolls back the complete speculative state and has no
/// capability to reach `output`; this keeps caller-owned statement trivia
/// available to the outer statement loop.
pub(crate) fn commit_header_statement<'parse, 'source, 'local, E, O>(
    mut probe: Probe<'parse, 'source, 'local, E>,
    output: O,
) -> Option<(
    HeaderStatementIntro<'source>,
    Committed<'parse, 'source, 'local, E, O>,
)>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = probe.input().checkpoint();
    let Some(intro) = probe.input().run(recognize_statement_intro) else {
        probe.input().rollback(checkpoint);
        return None;
    };
    let intro = match intro {
        StatementIntro::Use(intro) => HeaderStatementIntro::Use(intro),
        StatementIntro::Operator(intro) => HeaderStatementIntro::Operator(intro),
        StatementIntro::Binding(_) => {
            probe.input().rollback(checkpoint);
            return None;
        }
    };
    Some((intro, probe.commit(output)))
}

/// Parses either declaration family selected by the shared sink-free
/// introduction. Header and full callers invoke this same continuation; only
/// their [`CommitOutput`] differs.
pub(crate) fn parse_direct_header_declaration<'parse, 'source, 'local, E, O>(
    probe: Probe<'parse, 'source, 'local, E>,
    output: O,
) -> Option<(HeaderDeclaration<'source>, O)>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let (intro, mut committed) = commit_header_statement(probe, output)?;
    let declaration = match intro {
        HeaderStatementIntro::Use(intro) => {
            HeaderDeclaration::Use(commit_use_declaration(&mut committed, intro)?)
        }
        HeaderStatementIntro::Operator(intro) => {
            HeaderDeclaration::OperatorHeader(commit_operator_header(&mut committed, intro)?)
        }
    };
    Some((declaration, committed.into_output()))
}

pub(crate) fn recognize_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<StatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if binding_statement_selected(&mut i) {
        return i.run(recognize_binding_statement_intro).map(StatementIntro::Binding);
    }

    let start = i.pos();
    let first = i.run(scan_word)?;
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let trivia = scan_required_inline_trivia(&mut i)?;
        let keyword = i.run(scan_word)?;
        (Some(visibility), Some(trivia), keyword)
    } else {
        (None, None, first)
    };

    if keyword.text() == "use" {
        return Some(StatementIntro::Use(UseStatementIntro {
            start,
            visibility,
            after_visibility,
            use_keyword: keyword,
            after_use: scan_required_inline_trivia(&mut i)?,
        }));
    }

    let (lazy_keyword, after_lazy, fixity_keyword) = if keyword.text() == "lazy" {
        let trivia = scan_required_inline_trivia(&mut i)?;
        (Some(keyword), Some(trivia), i.run(scan_word)?)
    } else {
        (None, None, keyword)
    };
    let fixity = parse_operator_fixity(fixity_keyword)?;
    let after_fixity = scan_optional_inline_trivia(&mut i)?;

    Some(StatementIntro::Operator(OperatorStatementIntro {
        start,
        visibility,
        lazy_keyword,
        after_visibility,
        after_lazy,
        fixity_keyword,
        after_fixity,
        fixity,
    }))
}

/// Applies the binding-specific structural rule before visibility-prefixed
/// header spelling. `my use = value` is a binding, while `my use path` remains
/// an explicit-private use declaration.
fn binding_statement_selected<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let selected = (|| {
        let Some(my_keyword) = i.run(scan_word) else {
            return false;
        };
        if my_keyword.text() != "my" {
            return false;
        }
        let Some(after_my) = scan_required_inline_trivia(i) else {
            return true;
        };
        let Some(name) = i.run(scan_word) else {
            return true;
        };
        let Some(_) = scan_required_inline_trivia(i) else {
            return !matches!(name.text(), "use" | "lazy" | "prefix" | "infix" | "suffix" | "nullfix");
        };
        if i.input.remainder().starts_with('=') {
            return true;
        }
        let _ = after_my;
        !matches!(name.text(), "use" | "lazy" | "prefix" | "infix" | "suffix" | "nullfix")
    })();
    i.rollback(checkpoint);
    selected
}

fn visibility_prefix(word: WordSpan<'_>) -> Option<VisibilityPrefix<'_>> {
    let visibility = match word.text() {
        "pub" => Visibility::Public,
        "my" => Visibility::Private,
        "our" => Visibility::Our,
        _ => return None,
    };
    Some(VisibilityPrefix {
        visibility,
        keyword: word,
    })
}

fn scan_required_inline_trivia<E>(i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = i.run(scan_trivia)?;
    (!trivia.is_empty() && !i.input.source()[trivia.range()].contains(['\r', '\n']))
        .then_some(trivia)
}

fn scan_optional_inline_trivia<E>(i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = i.run(scan_trivia)?;
    (!i.input.source()[trivia.range()].contains(['\r', '\n'])).then_some(trivia)
}

fn emit_visibility<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    visibility: &VisibilityPrefix<'source>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let kind = match visibility.visibility {
        Visibility::Public => SyntaxKind::PubKw,
        Visibility::Private => SyntaxKind::MyKw,
        Visibility::Our => SyntaxKind::OurKw,
    };
    committed.token(kind, visibility.keyword.range());
}

/// Recognizes only the `my` prefix of a binding statement without giving the
/// speculative branch access to a CST or recovery sink.
pub(crate) fn recognize_binding_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<BindingStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let my_keyword = i.run(scan_word)?;
    (my_keyword.text() == "my").then_some(BindingStatementIntro { start, my_keyword })
}

/// Emits one complete binding declaration using the session's immutable Pratt
/// table. This valid-only precursor establishes the direct CST/data flow
/// without reconstructing an expression AST from the emitted tree; the next
/// recovery slice must make this continuation total before the root driver
/// calls it.
pub(crate) fn commit_binding_declaration<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: BindingStatementIntro<'source>,
) -> Option<ParsedBindingDeclaration<'source, O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::BindingStatement);
    committed.token(SyntaxKind::MyKw, intro.my_keyword.range());

    let after_my = commit_required_inline_trivia(committed)?;
    committed.emit_trivia(&after_my);
    let name = commit_word(committed)?;
    committed.token(SyntaxKind::Identifier, name.range());

    let after_name = commit_required_inline_trivia(committed)?;
    committed.emit_trivia(&after_name);
    let equals = commit_character(committed, '=')?;
    committed.token(SyntaxKind::Equals, equals);

    let after_equals = commit_required_inline_trivia(committed)?;
    let leading = if after_equals.is_empty() {
        LeadingTrivia::None
    } else {
        LeadingTrivia::Present
    };
    committed.emit_trivia(&after_equals);
    let value = parse_direct_expression_with_operators(operators, leading, committed)?;
    let range = intro.start..value.range().end;
    committed.finish_node();

    Some(ParsedBindingDeclaration { range, name, value })
}

/// Completes an accepted operator-header introduction while building its AST
/// and direct CST from the same scans.
pub(crate) fn commit_operator_header<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: OperatorStatementIntro<'source>,
) -> Option<OperatorHeaderDeclaration<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::OperatorHeader);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        committed.emit_trivia(intro.after_visibility.as_ref()?);
    }
    if let Some(lazy_keyword) = intro.lazy_keyword {
        committed.token(SyntaxKind::LazyKw, lazy_keyword.range());
        committed.emit_trivia(intro.after_lazy.as_ref()?);
    }
    committed.token(fixity_token_kind(intro.fixity), intro.fixity_keyword.range());
    committed.emit_trivia(&intro.after_fixity);

    let name = commit_operator_name(committed)?;
    let (left_binding_power, right_binding_power) = match intro.fixity {
        OperatorFixity::Nullfix => (None, None),
        OperatorFixity::Prefix => {
            emit_optional_inline_trivia(committed)?;
            (None, Some(commit_binding_power(committed)?))
        }
        OperatorFixity::Suffix => {
            emit_optional_inline_trivia(committed)?;
            (Some(commit_binding_power(committed)?), None)
        }
        OperatorFixity::Infix => {
            emit_optional_inline_trivia(committed)?;
            let left = commit_binding_power(committed)?;
            emit_optional_inline_trivia(committed)?;
            let right = commit_binding_power(committed)?;
            (Some(left), Some(right))
        }
    };
    emit_optional_inline_trivia(committed)?;
    let equals = commit_character(committed, '=')?;
    committed.token(SyntaxKind::Equals, equals.clone());
    committed.finish_node();

    Some(OperatorHeaderDeclaration {
        range: intro.start..equals.end,
        name,
        visibility: intro
            .visibility
            .as_ref()
            .map_or(Visibility::Private, |prefix| prefix.visibility),
        lazy: intro.lazy_keyword.is_some(),
        fixity: intro.fixity,
        left_binding_power,
        right_binding_power,
    })
}

fn fixity_token_kind(fixity: OperatorFixity) -> SyntaxKind {
    match fixity {
        OperatorFixity::Prefix => SyntaxKind::PrefixKw,
        OperatorFixity::Infix => SyntaxKind::InfixKw,
        OperatorFixity::Suffix => SyntaxKind::SuffixKw,
        OperatorFixity::Nullfix => SyntaxKind::NullfixKw,
    }
}

fn commit_operator_name<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<&'source str>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let (open, name, name_range, close) = committed.probe(|probe| {
        let i = probe.input();
        let open = scan_character(i, '(')?;
        let name_start = i.pos();
        let name = parse_operator_name(i)?;
        let name_range = name_start..i.pos();
        let close = scan_character(i, ')')?;
        Some((open, name, name_range, close))
    })?;

    committed.start_node(SyntaxKind::OperatorName);
    committed.token(SyntaxKind::LParen, open);
    committed.token(SyntaxKind::Operator, name_range);
    committed.token(SyntaxKind::RParen, close);
    committed.finish_node();
    Some(name)
}

fn commit_binding_power<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<BindingPower>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let (binding_power, components, dots) = committed.probe(|probe| {
        let i = probe.input();
        let mut values = Vec::new();
        let mut components = Vec::new();
        let mut dots = Vec::new();

        loop {
            let start = i.pos();
            while i
                .input
                .remainder()
                .chars()
                .next()
                .is_some_and(|character| character.is_ascii_digit())
            {
                i.input.next()?;
            }
            let end = i.pos();
            (start < end).then_some(())?;
            values.push(i.input.source()[start..end].parse::<i8>().ok()?);
            components.push(start..end);

            if !i.input.remainder().starts_with('.') {
                break;
            }
            dots.push(scan_character(i, '.')?);
        }

        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        let (first, rest) = values.split_first()?;
        Some((BindingPower::new(*first, rest.iter().copied()), components, dots))
    })?;

    committed.start_node(SyntaxKind::BindingPower);
    for (index, component) in components.into_iter().enumerate() {
        if index > 0 {
            committed.token(SyntaxKind::Dot, dots[index - 1].clone());
        }
        committed.token(SyntaxKind::Integer, component);
    }
    committed.finish_node();
    Some(binding_power)
}

fn commit_optional_inline_trivia<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| scan_optional_inline_trivia(probe.input()))
}

fn emit_optional_inline_trivia<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<()>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = commit_optional_inline_trivia(committed)?;
    committed.emit_trivia(&trivia);
    Some(())
}

fn commit_character<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    expected: char,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| scan_character(probe.input(), expected))
}

fn scan_character<E>(i: &mut SynIn<E>, expected: char) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    (i.input.remainder().starts_with(expected)).then_some(())?;
    i.input.next()?;
    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);
    Some(start..i.pos())
}

/// Completes an accepted `use` introduction while emitting every source token
/// in the owning declaration or recursive tree node that introduces it.
pub(crate) fn commit_use_declaration<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: UseStatementIntro<'source>,
) -> Option<UseDeclaration<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::UseDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        committed.emit_trivia(intro.after_visibility.as_ref()?);
    }
    committed.token(SyntaxKind::UseKw, intro.use_keyword.range());
    committed.emit_trivia(&intro.after_use);
    let tree = commit_use_tree(committed)?;
    committed.finish_node();

    Some(UseDeclaration {
        range: intro.start..tree.range().end,
        visibility: intro
            .visibility
            .as_ref()
            .map_or(Visibility::Private, |prefix| prefix.visibility),
        tree,
    })
}

fn commit_use_tree<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<UseTree<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = committed_position(committed);
    committed.start_node(SyntaxKind::UseTree);

    let (form, prefix, terminal, terminal_end, glob_aliases) = if let Some(open) = commit_maybe_character(committed, '{')? {
        let (terminal, end) = commit_use_group(committed, open)?;
        (HeaderImportForm::Plain, empty_use_path(), terminal, end, Vec::new())
    } else if let Some(first) = commit_maybe_operator_segment(committed)? {
        commit_use_path_and_terminal(committed, first, None, HeaderImportForm::Plain)?
    } else {
        let first = commit_word(committed)?;
        if first.text() == "mod" {
            committed.token(SyntaxKind::ModKw, first.range());
            let trivia = commit_required_inline_trivia(committed)?;
            committed.emit_trivia(&trivia);
            let first_segment = UseSegment::Word(commit_word(committed)?);
            commit_use_path_and_terminal(committed, first_segment, None, HeaderImportForm::Mod)?
        } else {
            let following_separator = commit_maybe_use_separator(committed)?;
            let form = classify_use_form(first, following_separator.as_ref().map(|(separator, _)| *separator));
            match form {
                HeaderImportForm::Plain => commit_use_path_and_terminal(
                    committed,
                    UseSegment::Word(first),
                    following_separator,
                    HeaderImportForm::Plain,
                )?,
                HeaderImportForm::Realm | HeaderImportForm::Band => {
                    committed.token(
                        if form == HeaderImportForm::Realm {
                            SyntaxKind::RealmKw
                        } else {
                            SyntaxKind::BandKw
                        },
                        first.range(),
                    );
                    let (_, marker_range) = following_separator?;
                    committed.token(separator_token_kind(form_marker_separator(form)), marker_range);
                    if let Some(open) = commit_maybe_character(committed, '{')? {
                        let (terminal, end) = commit_use_group(committed, open)?;
                        (form, empty_use_path(), terminal, end, Vec::new())
                    } else if let Some(star) = commit_maybe_character(committed, '*')? {
                        let (terminal, end, aliases) = commit_use_glob(committed, star)?;
                        (form, empty_use_path(), terminal, end, aliases)
                    } else {
                        let first_segment = commit_use_path_segment(committed)?;
                        commit_use_path_and_terminal(committed, first_segment, None, form)?
                    }
                }
                HeaderImportForm::Mod => unreachable!("mod was handled before marker classification"),
            }
        }
    };

    let aliases = match terminal {
        UseTerminal::Glob { .. } => glob_aliases,
        _ => commit_use_aliases(committed)?,
    };
    let qualifiers = commit_use_qualifiers(committed)?;
    let end = qualifiers_end(&qualifiers).unwrap_or_else(|| {
        aliases
            .last()
            .map_or(terminal_end, |alias| alias.range().end)
    });
    committed.finish_node();

    Some(UseTree {
        range: start..end,
        form,
        prefix,
        terminal,
        aliases,
        qualifiers,
    })
}

fn form_marker_separator(form: HeaderImportForm) -> UseSeparator {
    match form {
        HeaderImportForm::Realm => UseSeparator::Slash,
        HeaderImportForm::Band => UseSeparator::ColonColon,
        HeaderImportForm::Plain | HeaderImportForm::Mod => unreachable!("only markers have a marker separator"),
    }
}

fn commit_use_path_and_terminal<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    first: UseSegment<'source>,
    mut pending_separator: Option<(UseSeparator, Range<usize>)>,
    form: HeaderImportForm,
) -> Option<(
    HeaderImportForm,
    UsePath<'source>,
    UseTerminal<'source>,
    usize,
    Vec<WordSpan<'source>>,
)>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::UsePath);
    emit_use_segment(committed, &first);
    let mut path = UsePath {
        segments: vec![first],
        separators: Vec::new(),
    };

    loop {
        let Some((separator, range)) = pending_separator
            .take()
            .or(commit_maybe_use_separator(committed)?)
        else {
            committed.finish_node();
            let end = path.segments().last()?.range().end;
            return Some((form, path, UseTerminal::Single, end, Vec::new()));
        };
        if let Some(open) = commit_maybe_character(committed, '{')? {
            committed.finish_node();
            committed.token(separator_token_kind(separator), range);
            let (terminal, end) = commit_use_group(committed, open)?;
            return Some((
                form,
                path,
                terminal_with_join(terminal, separator),
                end,
                Vec::new(),
            ));
        }
        if let Some(star) = commit_maybe_character(committed, '*')? {
            committed.finish_node();
            committed.token(separator_token_kind(separator), range);
            let (terminal, end, aliases) = commit_use_glob(committed, star)?;
            return Some((
                form,
                path,
                terminal_with_join(terminal, separator),
                end,
                aliases,
            ));
        }
        committed.token(separator_token_kind(separator), range);
        path.separators.push(separator);
        let segment = commit_use_path_segment(committed)?;
        emit_use_segment(committed, &segment);
        path.segments.push(segment);
    }
}

fn terminal_with_join<'source>(terminal: UseTerminal<'source>, join: UseSeparator) -> UseTerminal<'source> {
    match terminal {
        UseTerminal::Group { items, .. } => UseTerminal::Group {
            join: Some(join),
            items,
        },
        UseTerminal::Glob { without, .. } => UseTerminal::Glob {
            join: Some(join),
            without,
        },
        UseTerminal::Single => unreachable!("only terminal nodes can receive a join"),
    }
}

fn separator_token_kind(separator: UseSeparator) -> SyntaxKind {
    match separator {
        UseSeparator::ColonColon => SyntaxKind::ColonColon,
        UseSeparator::Slash => SyntaxKind::Slash,
    }
}

fn commit_use_path_segment<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<UseSegment<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_maybe_operator_segment(committed)?.map_or_else(
        || commit_word(committed).map(UseSegment::Word),
        Some,
    )
}

fn emit_use_segment<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    segment: &UseSegment<'source>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    match segment {
        UseSegment::Word(word) => committed.token(SyntaxKind::Identifier, word.range()),
        UseSegment::Operator { range, .. } => {
            committed.start_node(SyntaxKind::OperatorName);
            committed.token(SyntaxKind::LParen, range.start..range.start + 1);
            committed.token(
                SyntaxKind::Operator,
                range.start + 1..range.end - 1,
            );
            committed.token(SyntaxKind::RParen, range.end - 1..range.end);
            committed.finish_node();
        }
    }
}

fn commit_use_group<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    open: Range<usize>,
) -> Option<(UseTerminal<'source>, usize)>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::UseGroup);
    committed.token(SyntaxKind::LBrace, open);
    let mut items = Vec::new();
    loop {
        let trivia = commit_trivia(committed)?;
        committed.emit_trivia(&trivia);
        if let Some(close) = commit_maybe_character(committed, '}')? {
            committed.token(SyntaxKind::RBrace, close.clone());
            committed.finish_node();
            return Some((UseTerminal::Group { join: None, items }, close.end));
        }
        items.push(commit_use_tree(committed)?);
        let trivia = commit_trivia(committed)?;
        let newline = trivia_has_newline(committed, &trivia);
        committed.emit_trivia(&trivia);
        if let Some(close) = commit_maybe_character(committed, '}')? {
            committed.token(SyntaxKind::RBrace, close.clone());
            committed.finish_node();
            return Some((UseTerminal::Group { join: None, items }, close.end));
        }
        if let Some(comma) = commit_maybe_character(committed, ',')? {
            committed.token(SyntaxKind::Comma, comma);
        } else if !newline {
            return None;
        }
    }
}

fn commit_use_glob<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    star: Range<usize>,
) -> Option<(UseTerminal<'source>, usize, Vec<WordSpan<'source>>)> 
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::UseGlob);
    committed.token(SyntaxKind::Star, star.clone());
    let aliases = commit_use_aliases(committed)?;
    let mut end = aliases.last().map_or(star.end, |alias| alias.range().end);
    let mut without = Vec::new();
    if let Some(prefix) = commit_maybe_without_prefix(committed)? {
        committed.emit_trivia(&prefix.leading);
        committed.token(SyntaxKind::WithoutKw, prefix.keyword.range());
        committed.emit_trivia(&prefix.after_keyword);
        without.push(commit_use_exclusion(committed)?);
        end = exclusion_range(without.last()?).end;
        while let Some(comma) = commit_maybe_character(committed, ',')? {
            committed.token(SyntaxKind::Comma, comma);
            let trivia = commit_trivia(committed)?;
            committed.emit_trivia(&trivia);
            without.push(commit_use_exclusion(committed)?);
            end = exclusion_range(without.last()?).end;
        }
    }
    committed.finish_node();
    Some((
        UseTerminal::Glob {
            join: None,
            without,
        },
        end,
        aliases,
    ))
}

fn commit_use_aliases<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Vec<WordSpan<'source>>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut aliases = Vec::new();
    while let Some(alias) = commit_maybe_use_alias(committed)? {
        committed.emit_trivia(&alias.leading);
        committed.start_node(SyntaxKind::UseAlias);
        committed.token(SyntaxKind::AsKw, alias.keyword.range());
        committed.emit_trivia(&alias.after_keyword);
        committed.token(SyntaxKind::Identifier, alias.name.range());
        committed.finish_node();
        aliases.push(alias.name);
    }
    Some(aliases)
}

fn commit_use_qualifiers<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<UseQualifiers<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let version = commit_maybe_version(committed)?;
    let anchor_prefix = commit_maybe_with_prefix(committed)?;
    if version.is_none() && anchor_prefix.is_none() {
        return Some(UseQualifiers::default());
    }
    committed.start_node(SyntaxKind::UseQualifiers);
    if let Some(version) = version {
        committed.emit_trivia(&version.leading);
        committed.start_node(SyntaxKind::UseVersion);
        committed.token(SyntaxKind::Version, version.value.range());
        committed.finish_node();
        let anchor = if let Some(prefix) = anchor_prefix {
            Some(commit_use_anchor(committed, prefix)?)
        } else {
            None
        };
        committed.finish_node();
        return Some(UseQualifiers {
            version: Some(version.value),
            anchor,
        });
    }
    let anchor = commit_use_anchor(committed, anchor_prefix?)?;
    committed.finish_node();
    Some(UseQualifiers {
        version: None,
        anchor: Some(anchor),
    })
}

fn commit_use_anchor<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    prefix: WithPrefix<'source>,
) -> Option<UsePath<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.emit_trivia(&prefix.leading);
    committed.start_node(SyntaxKind::UseAnchor);
    committed.token(SyntaxKind::WithKw, prefix.keyword.range());
    committed.emit_trivia(&prefix.after_keyword);
    committed.start_node(SyntaxKind::UsePath);
    let first = commit_word(committed)?;
    committed.token(SyntaxKind::Identifier, first.range());
    let mut path = UsePath {
        segments: vec![UseSegment::Word(first)],
        separators: Vec::new(),
    };
    while let Some((separator, range)) = commit_maybe_use_separator(committed)? {
        let segment = commit_word(committed)?;
        committed.token(separator_token_kind(separator), range);
        committed.token(SyntaxKind::Identifier, segment.range());
        path.separators.push(separator);
        path.segments.push(UseSegment::Word(segment));
    }
    committed.finish_node();
    committed.finish_node();
    Some(path)
}

fn commit_use_exclusion<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<UseExclusion<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = committed_position(committed);
    committed.start_node(SyntaxKind::UseExclusion);
    if let Some(segment) = commit_maybe_operator_segment(committed)? {
        emit_use_segment(committed, &segment);
        committed.finish_node();
        return Some(UseExclusion::Segment(segment));
    }
    if let Some(open) = commit_maybe_character(committed, '(')? {
        let group = commit_use_exclusion_group(committed, open, '(', ')')?;
        committed.finish_node();
        return Some(group);
    }
    if let Some(open) = commit_maybe_character(committed, '{')? {
        let group = commit_use_exclusion_group(committed, open, '{', '}')?;
        committed.finish_node();
        return Some(group);
    }
    if let Some(star) = commit_maybe_character(committed, '*')? {
        committed.token(SyntaxKind::Star, star.clone());
        committed.finish_node();
        return Some(UseExclusion::Glob { range: star });
    }
    let word = commit_word(committed)?;
    committed.token(SyntaxKind::Identifier, word.range());
    committed.finish_node();
    debug_assert_eq!(word.range().start, start);
    Some(UseExclusion::Segment(UseSegment::Word(word)))
}

fn commit_use_exclusion_group<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    open: Range<usize>,
    opening: char,
    closing: char,
) -> Option<UseExclusion<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = open.start;
    committed.start_node(SyntaxKind::UseExclusionGroup);
    committed.token(
        if opening == '(' {
            SyntaxKind::LParen
        } else {
            SyntaxKind::LBrace
        },
        open,
    );
    let mut items = Vec::new();
    loop {
        let trivia = commit_trivia(committed)?;
        committed.emit_trivia(&trivia);
        if let Some(close) = commit_maybe_character(committed, closing)? {
            committed.token(
                if closing == ')' {
                    SyntaxKind::RParen
                } else {
                    SyntaxKind::RBrace
                },
                close.clone(),
            );
            committed.finish_node();
            return Some(UseExclusion::Group {
                range: start..close.end,
                items,
            });
        }
        items.push(commit_use_tree(committed)?);
        let trivia = commit_trivia(committed)?;
        let newline = trivia_has_newline(committed, &trivia);
        committed.emit_trivia(&trivia);
        if let Some(close) = commit_maybe_character(committed, closing)? {
            committed.token(
                if closing == ')' {
                    SyntaxKind::RParen
                } else {
                    SyntaxKind::RBrace
                },
                close.clone(),
            );
            committed.finish_node();
            return Some(UseExclusion::Group {
                range: start..close.end,
                items,
            });
        }
        if let Some(comma) = commit_maybe_character(committed, ',')? {
            committed.token(SyntaxKind::Comma, comma);
        } else if !newline {
            return None;
        }
    }
}

#[derive(Clone)]
struct AliasPrefix<'source> {
    leading: TriviaRun,
    keyword: WordSpan<'source>,
    after_keyword: TriviaRun,
    name: WordSpan<'source>,
}

#[derive(Clone)]
struct VersionPrefix<'source> {
    leading: TriviaRun,
    value: UseVersion<'source>,
}

#[derive(Clone)]
struct WithPrefix<'source> {
    leading: TriviaRun,
    keyword: WordSpan<'source>,
    after_keyword: TriviaRun,
}

#[derive(Clone)]
struct WithoutPrefix<'source> {
    leading: TriviaRun,
    keyword: WordSpan<'source>,
    after_keyword: TriviaRun,
}

fn commit_maybe_use_alias<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Option<AliasPrefix<'source>>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let result = (|| {
            let leading = scan_required_inline_trivia(i)?;
            let keyword = i.run(scan_word)?;
            (keyword.text() == "as").then_some(())?;
            let after_keyword = scan_required_inline_trivia(i)?;
            let name = i.run(scan_word)?;
            Some(AliasPrefix {
                leading,
                keyword,
                after_keyword,
                name,
            })
        })();
        if result.is_none() {
            i.rollback(checkpoint);
        }
        Some(result)
    })
}

fn commit_maybe_version<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Option<VersionPrefix<'source>>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let result = (|| {
            let leading = scan_required_inline_trivia(i)?;
            let value = i.run(scan_use_version)?;
            Some(VersionPrefix { leading, value })
        })();
        if result.is_none() {
            i.rollback(checkpoint);
        }
        Some(result)
    })
}

fn commit_maybe_with_prefix<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Option<WithPrefix<'source>>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let result = (|| {
            let leading = scan_required_inline_trivia(i)?;
            let keyword = i.run(scan_word)?;
            (keyword.text() == "with").then_some(())?;
            let after_keyword = scan_required_inline_trivia(i)?;
            Some(WithPrefix {
                leading,
                keyword,
                after_keyword,
            })
        })();
        if result.is_none() {
            i.rollback(checkpoint);
        }
        Some(result)
    })
}

fn commit_maybe_without_prefix<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Option<WithoutPrefix<'source>>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let result = (|| {
            let leading = scan_required_inline_trivia(i)?;
            let keyword = i.run(scan_word)?;
            (keyword.text() == "without").then_some(())?;
            let after_keyword = scan_required_inline_trivia(i)?;
            Some(WithoutPrefix {
                leading,
                keyword,
                after_keyword,
            })
        })();
        if result.is_none() {
            i.rollback(checkpoint);
        }
        Some(result)
    })
}

fn qualifiers_end(qualifiers: &UseQualifiers<'_>) -> Option<usize> {
    qualifiers
        .anchor()
        .and_then(use_path_end)
        .or_else(|| qualifiers.version().map(|version| version.range().end))
}

fn committed_position<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> usize
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| probe.input().pos())
}

fn commit_word<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| probe.input().run(scan_word))
}

fn commit_trivia<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| probe.input().run(scan_trivia))
}

fn commit_required_inline_trivia<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| scan_required_inline_trivia(probe.input()))
}

fn trivia_has_newline<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    trivia: &TriviaRun,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']))
}

fn commit_maybe_character<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    expected: char,
) -> Option<Option<Range<usize>>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let result = scan_character(i, expected);
        if result.is_none() {
            i.rollback(checkpoint);
        }
        Some(result)
    })
}

fn commit_maybe_use_separator<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Option<(UseSeparator, Range<usize>)>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let result = i.run(scan_punctuation).and_then(|punctuation| match punctuation.kind() {
            PunctuationKind::ColonColon => Some((UseSeparator::ColonColon, punctuation.range())),
            PunctuationKind::Slash => Some((UseSeparator::Slash, punctuation.range())),
            _ => None,
        });
        if result.is_none() {
            i.rollback(checkpoint);
        }
        Some(result)
    })
}

fn commit_maybe_operator_segment<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Option<UseSegment<'source>>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let result = i.run(parse_parenthesized_use_operator);
        if result.is_none() {
            i.rollback(checkpoint);
        }
        Some(result)
    })
}

/// A `my name = value` declaration with a minimal expression value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BindingDeclaration<'source> {
    range: Range<usize>,
    name: WordSpan<'source>,
    value: Expression<'source>,
}

impl<'source> BindingDeclaration<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn name(&self) -> WordSpan<'source> {
        self.name
    }

    pub(crate) fn value(&self) -> &Expression<'source> {
        &self.value
    }
}

/// An operator signature before its opaque header body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OperatorHeaderDeclaration<'source> {
    range: Range<usize>,
    name: &'source str,
    visibility: Visibility,
    lazy: bool,
    fixity: OperatorFixity,
    left_binding_power: Option<BindingPower>,
    right_binding_power: Option<BindingPower>,
}

impl<'source> OperatorHeaderDeclaration<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn name(&self) -> &'source str {
        self.name
    }

    pub(crate) fn visibility(&self) -> Visibility {
        self.visibility
    }

    pub(crate) fn is_lazy(&self) -> bool {
        self.lazy
    }

    pub(crate) fn fixity(&self) -> OperatorFixity {
        self.fixity
    }

    pub(crate) fn left_binding_power(&self) -> Option<&BindingPower> {
        self.left_binding_power.as_ref()
    }

    pub(crate) fn right_binding_power(&self) -> Option<&BindingPower> {
        self.right_binding_power.as_ref()
    }

    pub(crate) fn to_header_operator(&self) -> HeaderOperator {
        let binding_power = match self.fixity {
            OperatorFixity::Prefix => BindingPowers::prefix(header_binding_power(
                self.right_binding_power
                    .as_ref()
                    .expect("prefix headers require a right binding power"),
            )),
            OperatorFixity::Infix => BindingPowers::infix(
                header_binding_power(
                    self.left_binding_power
                        .as_ref()
                        .expect("infix headers require a left binding power"),
                ),
                header_binding_power(
                    self.right_binding_power
                        .as_ref()
                        .expect("infix headers require a right binding power"),
                ),
            ),
            OperatorFixity::Suffix => BindingPowers::suffix(header_binding_power(
                self.left_binding_power
                    .as_ref()
                    .expect("suffix headers require a left binding power"),
            )),
            OperatorFixity::Nullfix => BindingPowers::nullfix(),
        };
        HeaderOperator::new(
            self.range(),
            self.name.to_owned(),
            self.fixity,
            self.visibility,
            self.lazy,
            binding_power,
        )
    }
}

fn header_binding_power(binding_power: &BindingPower) -> HeaderBindingPower {
    HeaderBindingPower::from_components(binding_power.components().to_vec())
}

/// A parsed `use` declaration before syntax planning resolves it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UseDeclaration<'source> {
    range: Range<usize>,
    visibility: Visibility,
    tree: UseTree<'source>,
}

impl<'source> UseDeclaration<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn visibility(&self) -> Visibility {
        self.visibility
    }

    pub(crate) fn tree(&self) -> &UseTree<'source> {
        &self.tree
    }

    /// Projects one qualifier-free single-target use declaration to a header fact.
    pub(crate) fn project_single_import(&self) -> Result<HeaderImport, UseSingleProjectionError> {
        if !matches!(self.tree.terminal, UseTerminal::Single) {
            return Err(UseSingleProjectionError::NonSingleTerminal);
        }
        if !self.tree.qualifiers.is_empty() {
            return Err(UseSingleProjectionError::Qualifiers);
        }
        let alias = match self.tree.aliases.as_slice() {
            [] => None,
            [alias] => Some(alias.text().to_owned()),
            _ => return Err(UseSingleProjectionError::MultipleAliases),
        };

        Ok(HeaderImport::new(
            self.range(),
            self.tree.form,
            project_use_route(&self.tree.prefix),
            self.visibility,
            alias,
        ))
    }

    /// Expands every complete single-target leaf in source order.
    pub(crate) fn expand_header_imports(&self) -> Vec<Result<HeaderImport, UseExpansionError>> {
        expand_use_tree(
            &self.tree,
            HeaderImportForm::Plain,
            &HeaderImportRoute::new(Vec::new(), Vec::new()),
            None,
            self.visibility,
            Some(self.range()),
        )
    }
}

/// Why a use declaration cannot yet project to one header import fact.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum UseSingleProjectionError {
    NonSingleTerminal,
    MultipleAliases,
    Qualifiers,
}

/// Why one use-tree branch cannot produce a complete header import fact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum UseExpansionError {
    FormConflict {
        range: Range<usize>,
        inherited_form: HeaderImportForm,
        form: HeaderImportForm,
    },
    GroupAlias {
        range: Range<usize>,
    },
    MultipleAliases {
        range: Range<usize>,
    },
    Qualifiers {
        range: Range<usize>,
    },
    UnsupportedGlob {
        range: Range<usize>,
    },
    MissingRouteJoin {
        range: Range<usize>,
    },
    MissingTarget {
        range: Range<usize>,
    },
}

/// One recursively composable `use` specification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UseTree<'source> {
    range: Range<usize>,
    form: HeaderImportForm,
    prefix: UsePath<'source>,
    terminal: UseTerminal<'source>,
    aliases: Vec<WordSpan<'source>>,
    qualifiers: UseQualifiers<'source>,
}

impl<'source> UseTree<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn form(&self) -> HeaderImportForm {
        self.form
    }

    pub(crate) fn prefix(&self) -> &UsePath<'source> {
        &self.prefix
    }

    pub(crate) fn terminal(&self) -> &UseTerminal<'source> {
        &self.terminal
    }

    pub(crate) fn aliases(&self) -> &[WordSpan<'source>] {
        &self.aliases
    }

    pub(crate) fn qualifiers(&self) -> &UseQualifiers<'source> {
        &self.qualifiers
    }
}

/// A separator-preserving path prefix of a use specification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UsePath<'source> {
    segments: Vec<UseSegment<'source>>,
    separators: Vec<UseSeparator>,
}

impl<'source> UsePath<'source> {
    pub(crate) fn segments(&self) -> &[UseSegment<'source>] {
        &self.segments
    }

    pub(crate) fn separators(&self) -> &[UseSeparator] {
        &self.separators
    }
}

/// One path segment, retaining the distinction between words and operators.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum UseSegment<'source> {
    Word(WordSpan<'source>),
    Operator {
        range: Range<usize>,
        text: &'source str,
    },
}

impl<'source> UseSegment<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        match self {
            Self::Word(word) => word.range(),
            Self::Operator { range, .. } => range.clone(),
        }
    }
}

fn project_use_route(path: &UsePath<'_>) -> HeaderImportRoute {
    let segments = path
        .segments()
        .iter()
        .map(|segment| match segment {
            UseSegment::Word(word) => word.text().to_owned(),
            UseSegment::Operator { text, .. } => (*text).to_owned(),
        })
        .collect();
    let separators = path
        .separators()
        .iter()
        .map(|separator| match separator {
            UseSeparator::ColonColon => HeaderImportRouteSeparator::ColonColon,
            UseSeparator::Slash => HeaderImportRouteSeparator::Slash,
        })
        .collect();

    HeaderImportRoute::new(segments, separators)
}

fn expand_use_tree(
    tree: &UseTree<'_>,
    inherited_form: HeaderImportForm,
    inherited_route: &HeaderImportRoute,
    pending_join: Option<UseSeparator>,
    visibility: Visibility,
    root_range: Option<Range<usize>>,
) -> Vec<Result<HeaderImport, UseExpansionError>> {
    let effective_form = if tree.form == HeaderImportForm::Plain {
        inherited_form
    } else if inherited_route.segments().is_empty() {
        tree.form
    } else {
        return vec![Err(UseExpansionError::FormConflict {
            range: tree.range(),
            inherited_form,
            form: tree.form,
        })];
    };
    if !tree.qualifiers.is_empty() {
        return vec![Err(UseExpansionError::Qualifiers {
            range: tree.range(),
        })];
    }

    let route = match concatenate_use_route(inherited_route, pending_join, &tree.prefix) {
        Ok(route) => route,
        Err(error) => return vec![Err(error)],
    };

    match &tree.terminal {
        UseTerminal::Single => {
            if route.segments().is_empty() {
                return vec![Err(UseExpansionError::MissingTarget {
                    range: tree.range(),
                })];
            }
            let alias = match tree.aliases.as_slice() {
                [] => None,
                [alias] => Some(alias.text().to_owned()),
                _ => {
                    return vec![Err(UseExpansionError::MultipleAliases {
                        range: tree.range(),
                    })];
                }
            };
            let range = root_range.unwrap_or_else(|| tree.range());
            vec![Ok(HeaderImport::new(
                range,
                effective_form,
                route,
                visibility,
                alias,
            ))]
        }
        UseTerminal::Group { join, items } => {
            if !tree.aliases.is_empty() {
                return vec![Err(UseExpansionError::GroupAlias {
                    range: tree.range(),
                })];
            }
            items
                .iter()
                .flat_map(|item| {
                    expand_use_tree(item, effective_form, &route, *join, visibility, None)
                })
                .collect()
        }
        UseTerminal::Glob { .. } => vec![Err(UseExpansionError::UnsupportedGlob {
            range: tree.range(),
        })],
    }
}

fn concatenate_use_route(
    inherited: &HeaderImportRoute,
    pending_join: Option<UseSeparator>,
    suffix: &UsePath<'_>,
) -> Result<HeaderImportRoute, UseExpansionError> {
    let mut segments = inherited.segments().to_vec();
    let mut separators = inherited.separators().to_vec();

    if !suffix.segments().is_empty() {
        if !segments.is_empty() {
            let Some(join) = pending_join else {
                return Err(UseExpansionError::MissingRouteJoin {
                    range: suffix.segments()[0].range(),
                });
            };
            separators.push(project_use_separator(join));
        }
        let suffix_route = project_use_route(suffix);
        segments.extend_from_slice(suffix_route.segments());
        separators.extend_from_slice(suffix_route.separators());
    }

    Ok(HeaderImportRoute::new(segments, separators))
}

fn project_use_separator(separator: UseSeparator) -> HeaderImportRouteSeparator {
    match separator {
        UseSeparator::ColonColon => HeaderImportRouteSeparator::ColonColon,
        UseSeparator::Slash => HeaderImportRouteSeparator::Slash,
    }
}

/// A route separator between two stored path segments.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum UseSeparator {
    ColonColon,
    Slash,
}

/// The terminating shape of a use tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum UseTerminal<'source> {
    Single,
    Group {
        join: Option<UseSeparator>,
        items: Vec<UseTree<'source>>,
    },
    Glob {
        join: Option<UseSeparator>,
        without: Vec<UseExclusion<'source>>,
    },
}

/// Syntactic qualifiers whose resolution semantics are intentionally deferred.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct UseQualifiers<'source> {
    version: Option<UseVersion<'source>>,
    anchor: Option<UsePath<'source>>,
}

impl<'source> UseQualifiers<'source> {
    pub(crate) fn version(&self) -> Option<&UseVersion<'source>> {
        self.version.as_ref()
    }

    pub(crate) fn anchor(&self) -> Option<&UsePath<'source>> {
        self.anchor.as_ref()
    }

    fn is_empty(&self) -> bool {
        self.version.is_none() && self.anchor.is_none()
    }
}

/// A raw version suffix on a use specification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UseVersion<'source> {
    range: Range<usize>,
    text: &'source str,
}

impl<'source> UseVersion<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn text(&self) -> &'source str {
        self.text
    }
}

/// An exclusion pattern attached to a glob terminal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum UseExclusion<'source> {
    Segment(UseSegment<'source>),
    Glob {
        range: Range<usize>,
    },
    Group {
        range: Range<usize>,
        items: Vec<UseTree<'source>>,
    },
}

/// Parses one leading `use` declaration from the shared character stream.
pub(crate) fn parse_declaration<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Declaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.choice((
        parse_use_declaration.map(Declaration::Use),
        parse_binding_declaration.map(Declaration::Binding),
        parse_operator_header.map(Declaration::OperatorHeader),
    ))
}

/// Parses only declaration forms that are valid in the source-leading header.
///
/// Binding declarations intentionally remain absent: encountering one ends
/// header discovery without making it a syntax error.
pub(crate) fn parse_header_declaration<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<HeaderDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.choice((
        parse_use_declaration.map(HeaderDeclaration::Use),
        parse_operator_header.map(HeaderDeclaration::OperatorHeader),
    ))
}

fn parse_operator_header<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<OperatorHeaderDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let first = i.run(scan_word)?;
    let (visibility, fixity_keyword) = match first.text() {
        "pub" => (
            Visibility::Public,
            parse_operator_header_word_after_trivia(&mut i)?,
        ),
        "my" => (
            Visibility::Private,
            parse_operator_header_word_after_trivia(&mut i)?,
        ),
        "our" => (
            Visibility::Our,
            parse_operator_header_word_after_trivia(&mut i)?,
        ),
        _ => (Visibility::Private, first),
    };
    let (lazy, fixity_keyword) = if fixity_keyword.text() == "lazy" {
        (true, parse_operator_header_word_after_trivia(&mut i)?)
    } else {
        (false, fixity_keyword)
    };
    let fixity = parse_operator_fixity(fixity_keyword)?;

    optional_inline_trivia(&mut i)?;
    let open = i.run(scan_punctuation)?;
    (open.kind() == PunctuationKind::Open(Delimiter::Parenthesis)).then_some(())?;
    let name = parse_operator_name(&mut i)?;
    let close = i.run(scan_punctuation)?;
    (close.kind() == PunctuationKind::Close(Delimiter::Parenthesis)).then_some(())?;

    let (left_binding_power, right_binding_power) = match fixity {
        OperatorFixity::Nullfix => (None, None),
        OperatorFixity::Prefix => {
            optional_inline_trivia(&mut i)?;
            (None, Some(i.run(parse_binding_power)?))
        }
        OperatorFixity::Suffix => {
            optional_inline_trivia(&mut i)?;
            (Some(i.run(parse_binding_power)?), None)
        }
        OperatorFixity::Infix => {
            optional_inline_trivia(&mut i)?;
            let left = i.run(parse_binding_power)?;
            optional_inline_trivia(&mut i)?;
            let right = i.run(parse_binding_power)?;
            (Some(left), Some(right))
        }
    };
    optional_inline_trivia(&mut i)?;
    i.skip(chasa::prelude::item('='))?;
    let end = i.pos();

    Some(OperatorHeaderDeclaration {
        range: start..end,
        name,
        visibility,
        lazy,
        fixity,
        left_binding_power,
        right_binding_power,
    })
}

fn parse_operator_header_word_after_trivia<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    inline_trivia(i)?;
    i.run(scan_word)
}

fn parse_operator_fixity(word: WordSpan<'_>) -> Option<OperatorFixity> {
    match word.text() {
        "prefix" => Some(OperatorFixity::Prefix),
        "infix" => Some(OperatorFixity::Infix),
        "suffix" => Some(OperatorFixity::Suffix),
        "nullfix" => Some(OperatorFixity::Nullfix),
        _ => None,
    }
}

fn parse_operator_name<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<&'source str>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = i.pos();
    while let Some(character) = i.input.remainder().chars().next() {
        if character == ')' {
            break;
        }
        (!character.is_whitespace()
            && !matches!(
                character,
                '(' | '[' | ']' | '{' | '}' | '\\' | ',' | ';' | '"' | '\''
            ))
        .then_some(())?;
        i.input.next()?;
    }
    let end = i.pos();
    (start < end).then_some(&i.input.source()[start..end])
}

/// Parses the dot-separated binding-power vector used by operator headers.
fn parse_binding_power<E>(
    i: SynIn<E>,
) -> Option<BindingPower>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut components = Vec::new();

    loop {
        let start = i.pos();
        while i
            .input
            .remainder()
            .chars()
            .next()
            .is_some_and(|character| character.is_ascii_digit())
        {
            i.input.next()?;
        }
        let end = i.pos();
        (start < end).then_some(())?;
        components.push(i.input.source()[start..end].parse::<i8>().ok()?);

        if !i.input.remainder().starts_with('.') {
            break;
        }
        i.input.next()?;
    }

    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);

    let (first, rest) = components.split_first()?;
    Some(BindingPower::new(*first, rest.iter().copied()))
}

fn parse_binding_declaration<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<BindingDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let keyword = i.run(scan_word)?;
    (keyword.text() == "my").then_some(())?;
    inline_trivia(&mut i)?;
    let name = i.run(scan_word)?;
    inline_trivia(&mut i)?;
    i.skip(chasa::prelude::item('='))?;
    inline_trivia(&mut i)?;
    let value = i.run(parse_expression)?;
    let end = value.range().end;

    Some(BindingDeclaration {
        range: start..end,
        name,
        value,
    })
}

fn parse_use_declaration<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<UseDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let keyword = i.run(scan_word)?;
    (keyword.text() == "use").then_some(())?;
    inline_trivia(&mut i)?;

    let tree = parse_use_tree(&mut i)?;
    let end = tree.range().end;

    Some(UseDeclaration {
        range: start..end,
        visibility: Visibility::Private,
        tree,
    })
}

fn parse_use_tree<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<UseTree<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    if i.maybe(from_fn(parse_open_brace))?.is_some() {
        let (terminal, terminal_end) = parse_use_group_terminal(i, None)?;
        let aliases = parse_use_aliases(i)?;
        let alias_end = aliases
            .last()
            .map_or(terminal_end, |alias| alias.range().end);
        let (qualifiers, qualifier_end) = parse_use_qualifiers(i)?;
        let end = qualifier_end.unwrap_or(alias_end);
        return Some(UseTree {
            range: start..end,
            form: HeaderImportForm::Plain,
            prefix: empty_use_path(),
            terminal,
            aliases,
            qualifiers,
        });
    }

    if let Some(first) = i.maybe(from_fn(parse_parenthesized_use_operator))? {
        let (prefix, terminal, terminal_end) = parse_use_path_and_terminal(i, first, None)?;
        return finish_use_tree(
            i,
            start,
            HeaderImportForm::Plain,
            prefix,
            terminal,
            terminal_end,
        );
    }

    let first = i.run(scan_word)?;

    let (form, prefix, mut terminal, terminal_end) = if classify_use_form(first, None)
        == HeaderImportForm::Mod
    {
        inline_trivia(i)?;
        let first_segment = parse_use_path_segment(i)?;
        let (prefix, terminal, terminal_end) = parse_use_path_and_terminal(i, first_segment, None)?;
        (HeaderImportForm::Mod, prefix, terminal, terminal_end)
    } else {
        let following_separator = i.maybe(from_fn(parse_use_separator))?;
        match classify_use_form(first, following_separator) {
            HeaderImportForm::Realm | HeaderImportForm::Band => {
                let form = classify_use_form(first, following_separator);
                if i.maybe(from_fn(parse_open_brace))?.is_some() {
                    let (terminal, terminal_end) = parse_use_group_terminal(i, None)?;
                    (form, empty_use_path(), terminal, terminal_end)
                } else {
                    let first_segment = parse_use_path_segment(i)?;
                    let (prefix, terminal, terminal_end) =
                        parse_use_path_and_terminal(i, first_segment, None)?;
                    (form, prefix, terminal, terminal_end)
                }
            }
            HeaderImportForm::Plain => {
                let (prefix, terminal, terminal_end) =
                    parse_use_path_and_terminal(i, UseSegment::Word(first), following_separator)?;
                (HeaderImportForm::Plain, prefix, terminal, terminal_end)
            }
            HeaderImportForm::Mod => unreachable!("mod is handled before separator classification"),
        }
    };
    finish_use_tree(i, start, form, prefix, terminal, terminal_end)
}

fn finish_use_tree<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
    start: usize,
    form: HeaderImportForm,
    prefix: UsePath<'source>,
    mut terminal: UseTerminal<'source>,
    terminal_end: usize,
) -> Option<UseTree<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let aliases = parse_use_aliases(i)?;
    let tail_end = aliases
        .last()
        .map_or(terminal_end, |alias| alias.range().end);
    let without_end = if let UseTerminal::Glob { without, .. } = &mut terminal {
        parse_use_without(i)?.map(|(parsed_without, end)| {
            *without = parsed_without;
            end
        })
    } else {
        None
    };
    let qualifier_input_end = without_end.unwrap_or(tail_end);
    let (qualifiers, qualifier_end) = parse_use_qualifiers(i)?;
    let end = qualifier_end.unwrap_or(qualifier_input_end);

    Some(UseTree {
        range: start..end,
        form,
        prefix,
        terminal,
        aliases,
        qualifiers,
    })
}

fn classify_use_form(
    first: WordSpan<'_>,
    following_separator: Option<UseSeparator>,
) -> HeaderImportForm {
    if first.text() == "mod" {
        HeaderImportForm::Mod
    } else if first.text() == "realm" && following_separator == Some(UseSeparator::Slash) {
        HeaderImportForm::Realm
    } else if first.text() == "band" && following_separator == Some(UseSeparator::ColonColon) {
        HeaderImportForm::Band
    } else {
        HeaderImportForm::Plain
    }
}

fn parse_use_path_and_terminal<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
    first: UseSegment<'source>,
    first_separator: Option<UseSeparator>,
) -> Option<(UsePath<'source>, UseTerminal<'source>, usize)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut path = UsePath {
        segments: vec![first],
        separators: Vec::new(),
    };
    let mut pending_separator = first_separator;

    loop {
        let Some(current) = pending_separator
            .take()
            .or(i.maybe(from_fn(parse_use_separator))?)
        else {
            break;
        };
        if i.maybe(from_fn(parse_open_brace))?.is_some() {
            let (terminal, terminal_end) = parse_use_group_terminal(i, Some(current))?;
            return Some((path, terminal, terminal_end));
        }
        if let Some(range) = i.maybe(from_fn(parse_use_glob))? {
            return Some((
                path,
                UseTerminal::Glob {
                    join: Some(current),
                    without: Vec::new(),
                },
                range.end,
            ));
        }
        path.separators.push(current);
        path.segments.push(parse_use_path_segment(i)?);
    }

    debug_assert_eq!(
        path.separators.len(),
        path.segments.len().saturating_sub(1),
        "a use path has one separator between each stored segment"
    );
    let end = path
        .segments()
        .last()
        .expect("use paths always contain their first segment")
        .range()
        .end;
    Some((path, UseTerminal::Single, end))
}

fn parse_use_group_terminal<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
    join: Option<UseSeparator>,
) -> Option<(UseTerminal<'source>, usize)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut items = Vec::new();

    loop {
        consume_group_trivia(i)?;
        if let Some(close) = i.maybe(from_fn(parse_close_brace))? {
            return Some((UseTerminal::Group { join, items }, close.end));
        }

        items.push(parse_use_tree(i)?);

        let separator_has_newline = consume_group_trivia(i)?;
        if let Some(close) = i.maybe(from_fn(parse_close_brace))? {
            return Some((UseTerminal::Group { join, items }, close.end));
        }
        if i.maybe(from_fn(parse_comma))?.is_some() || separator_has_newline {
            continue;
        }
        return None;
    }
}

fn parse_use_aliases<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<Vec<WordSpan<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut aliases = Vec::new();
    while let Some(alias) = i.maybe(from_fn(parse_use_alias))? {
        aliases.push(alias);
    }
    Some(aliases)
}

fn parse_use_alias<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    inline_trivia(&mut i)?;
    let keyword = i.run(scan_word)?;
    (keyword.text() == "as").then_some(())?;
    inline_trivia(&mut i)?;
    i.run(scan_word)
}

fn parse_use_qualifiers<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<(UseQualifiers<'source>, Option<usize>)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let version = i.maybe(from_fn(parse_use_version_suffix))?;
    let anchor = parse_use_anchor(i)?;
    let end = anchor
        .as_ref()
        .and_then(use_path_end)
        .or_else(|| version.as_ref().map(|version| version.range.end));

    Some((UseQualifiers { version, anchor }, end))
}

fn parse_use_version_suffix<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<UseVersion<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    inline_trivia(&mut i)?;
    i.run(scan_use_version)
}

fn scan_use_version<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<UseVersion<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = i.pos();
    i.skip(chasa::prelude::item('v'))?;
    i.input
        .remainder()
        .chars()
        .next()
        .is_some_and(|character| character.is_ascii_digit())
        .then_some(())?;
    i.input.next()?;

    while i.input.remainder().chars().next().is_some_and(|character| {
        character.is_ascii_alphanumeric() || matches!(character, '.' | '-' | '+')
    }) {
        i.input.next()?;
    }

    let end = i.pos();
    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);

    Some(UseVersion {
        range: start..end,
        text: &i.input.source()[start..end],
    })
}

fn parse_use_anchor<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<Option<UsePath<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let Some(()) = i.maybe(from_fn(parse_with_keyword))? else {
        return Some(None);
    };
    inline_trivia(i)?;

    let first = i.run(scan_word)?;
    let mut path = UsePath {
        segments: vec![UseSegment::Word(first)],
        separators: Vec::new(),
    };

    while let Some(separator) = i.maybe(from_fn(parse_use_separator))? {
        path.separators.push(separator);
        path.segments.push(UseSegment::Word(i.run(scan_word)?));
    }

    debug_assert_eq!(
        path.separators.len(),
        path.segments.len().saturating_sub(1),
        "an anchor path has one separator between each identifier segment"
    );
    Some(Some(path))
}

fn parse_with_keyword<E>(mut i: SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    inline_trivia(&mut i)?;
    let keyword = i.run(scan_word)?;
    (keyword.text() == "with").then_some(())
}

fn use_path_end(path: &UsePath<'_>) -> Option<usize> {
    path.segments().last().map(|segment| segment.range().end)
}

fn parse_use_without<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<Option<(Vec<UseExclusion<'source>>, usize)>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.maybe(from_fn(parse_use_without_clause))
}

fn parse_use_without_clause<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<(Vec<UseExclusion<'source>>, usize)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    inline_trivia(&mut i)?;
    let keyword = i.run(scan_word)?;
    (keyword.text() == "without").then_some(())?;
    inline_trivia(&mut i)?;

    let mut exclusions = vec![parse_use_exclusion(&mut i)?];
    while i.maybe(from_fn(parse_comma))?.is_some() {
        i.run(scan_trivia)?;
        exclusions.push(parse_use_exclusion(&mut i)?);
    }
    let end = exclusion_range(exclusions.last().expect("without has one exclusion")).end;

    Some((exclusions, end))
}

fn parse_use_exclusion<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<UseExclusion<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(segment) = i.maybe(from_fn(parse_parenthesized_use_operator))? {
        return Some(UseExclusion::Segment(segment));
    }
    if let Some(group) = i.maybe(from_fn(parse_use_exclusion_group))? {
        return Some(group);
    }
    if let Some(range) = i.maybe(from_fn(parse_use_glob))? {
        return Some(UseExclusion::Glob { range });
    }

    i.run(scan_word)
        .map(|word| UseExclusion::Segment(UseSegment::Word(word)))
}

fn parse_parenthesized_use_operator<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<UseSegment<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let open = i.run(scan_open_parenthesis)?;
    let start = i.pos();

    while let Some(character) = i.input.remainder().chars().next() {
        if character == ')' {
            break;
        }
        is_use_operator_character(character).then_some(())?;
        i.input.next()?;
    }

    let end = i.pos();
    (start < end).then_some(())?;
    i.run(scan_close_parenthesis)?;
    Some(UseSegment::Operator {
        range: open.start..i.pos(),
        text: &i.input.source()[start..end],
    })
}

/// Recognizes either spelling permitted in normal use-path segment slots.
///
/// Parenthesized operators are deliberately tried before words so `(+)` is
/// retained as one operator segment rather than being left to a terminal
/// group branch. Both the spec-start and separator-target callers use this
/// shared recognizer.
fn parse_use_path_segment<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<UseSegment<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(segment) = i.maybe(from_fn(parse_parenthesized_use_operator))? {
        return Some(segment);
    }
    i.run(scan_word).map(UseSegment::Word)
}

fn is_use_operator_character(character: char) -> bool {
    !character.is_whitespace()
        && character != '_'
        && !unicode_ident::is_xid_continue(character)
        && !matches!(
            character,
            '(' | ')' | '[' | ']' | '{' | '}' | ',' | ':' | '/' | ';'
        )
}

fn parse_use_exclusion_group<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<UseExclusion<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let open = i.run(scan_punctuation)?;
    let delimiter = match open.kind() {
        PunctuationKind::Open(Delimiter::Parenthesis) => Delimiter::Parenthesis,
        PunctuationKind::Open(Delimiter::Brace) => Delimiter::Brace,
        _ => return None,
    };
    let start = open.range().start;
    let mut items = Vec::new();

    loop {
        consume_group_trivia(&mut i)?;
        if let Some(close) = i.maybe(from_fn(|i| parse_close_delimiter(delimiter, i)))? {
            return Some(UseExclusion::Group {
                range: start..close.end,
                items,
            });
        }

        items.push(parse_use_tree(&mut i)?);

        let separator_has_newline = consume_group_trivia(&mut i)?;
        if let Some(close) = i.maybe(from_fn(|i| parse_close_delimiter(delimiter, i)))? {
            return Some(UseExclusion::Group {
                range: start..close.end,
                items,
            });
        }
        if i.maybe(from_fn(parse_comma))?.is_some() || separator_has_newline {
            continue;
        }
        return None;
    }
}

fn parse_use_glob<E>(mut i: SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = i.pos();
    i.skip(chasa::prelude::item('*'))?;
    let end = i.pos();

    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);

    Some(start..end)
}

fn exclusion_range(exclusion: &UseExclusion<'_>) -> Range<usize> {
    match exclusion {
        UseExclusion::Segment(segment) => segment.range(),
        UseExclusion::Glob { range } | UseExclusion::Group { range, .. } => range.clone(),
    }
}

fn empty_use_path<'source>() -> UsePath<'source> {
    UsePath {
        segments: Vec::new(),
        separators: Vec::new(),
    }
}

fn consume_group_trivia<E>(i: &mut SynIn<E>) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = i.run(scan_trivia)?;
    Some(i.input.source()[trivia.range()].contains(['\r', '\n']))
}

fn parse_open_brace<E>(mut i: SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Open(Delimiter::Brace)).then_some(())
}

fn scan_open_parenthesis<E>(
    mut i: SynIn<E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Open(Delimiter::Parenthesis))
        .then(|| punctuation.range())
}

fn scan_close_parenthesis<E>(mut i: SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Close(Delimiter::Parenthesis)).then_some(())
}

fn parse_close_delimiter<E>(
    delimiter: Delimiter,
    mut i: SynIn<E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Close(delimiter)).then(|| punctuation.range())
}

fn parse_close_brace<E>(
    mut i: SynIn<E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Close(Delimiter::Brace)).then(|| punctuation.range())
}

fn parse_comma<E>(mut i: SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Comma).then_some(())
}

fn parse_use_separator<E>(
    mut i: SynIn<E>,
) -> Option<UseSeparator>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    match punctuation.kind() {
        PunctuationKind::ColonColon => Some(UseSeparator::ColonColon),
        PunctuationKind::Slash => Some(UseSeparator::Slash),
        _ => None,
    }
}

fn inline_trivia<E>(i: &mut SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = i.run(scan_trivia)?;
    let text = &i.input.source()[trivia.range()];
    (!text.is_empty() && !text.contains(['\r', '\n'])).then_some(())
}

fn optional_inline_trivia<E>(i: &mut SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = i.run(scan_trivia)?;
    (!i.input.source()[trivia.range()].contains(['\r', '\n'])).then_some(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use chasa::{input::IsCut, prelude::In};
    use std::{cell::RefCell, rc::Rc};

    use crate::{
        SyntaxNode,
        input::SourceInput,
        session::{
            CommitOutput, CommittedRecoveryRecord, FullCstOutput, HeaderOutput, ParseLocal,
            Probe,
        },
    };

    const LEADING_USE_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/leading-use-plain/main.yu"
    ));
    const LEADING_MOD_USE_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/leading-use-mod/main.yu"
    ));
    const LEADING_REALM_USE_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/leading-use-realm/main.yu"
    ));
    const LEADING_BAND_USE_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/leading-use-band/main.yu"
    ));
    const INFIX_OPERATOR_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/infix-operator-header/main.yu"
    ));

    #[derive(Clone, Debug, Eq, PartialEq)]
    enum OutputCall {
        Start(SyntaxKind),
        Token(SyntaxKind, Range<usize>),
        Finish,
    }

    struct RecordingOutput {
        calls: Rc<RefCell<Vec<OutputCall>>>,
    }

    impl CommitOutput<'_> for RecordingOutput {
        type Checkpoint = usize;

        fn checkpoint(&mut self) -> Self::Checkpoint {
            self.calls.borrow().len()
        }

        fn start_node(&mut self, kind: SyntaxKind) {
            self.calls.borrow_mut().push(OutputCall::Start(kind));
        }

        fn start_node_at(&mut self, _: Self::Checkpoint, kind: SyntaxKind) {
            self.calls.borrow_mut().push(OutputCall::Start(kind));
        }

        fn token(&mut self, kind: SyntaxKind, range: Range<usize>) {
            self.calls.borrow_mut().push(OutputCall::Token(kind, range));
        }

        fn emit_trivia(&mut self, _: &TriviaRun) {}

        fn finish_node(&mut self) {
            self.calls.borrow_mut().push(OutputCall::Finish);
        }

            fn commit_recovery(&mut self, _: CommittedRecoveryRecord) {}

            fn emit_missing(&mut self, _: CommittedRecoveryRecord) {}

            fn emit_error(&mut self, _: CommittedRecoveryRecord) {}
        }

    fn parse_direct_operator_with_output<'source, O>(
        source: &'source str,
        output: O,
    ) -> (OperatorHeaderDeclaration<'source>, O)
    where
        O: CommitOutput<'source>,
    {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let (intro, mut committed) = commit_header_statement(Probe::new(i), output)
            .expect("source has an operator header introduction");
        let HeaderStatementIntro::Operator(intro) = intro else {
            panic!("source did not select the operator continuation");
        };
        let declaration = commit_operator_header(&mut committed, intro)
            .expect("operator continuation should parse the source");
        (declaration, committed.into_output())
    }

    fn parse_direct_use_with_output<'source, O>(
        source: &'source str,
        output: O,
    ) -> (UseDeclaration<'source>, O)
    where
        O: CommitOutput<'source>,
    {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let (intro, mut committed) = commit_header_statement(Probe::new(i), output)
            .expect("source has a use declaration introduction");
        let HeaderStatementIntro::Use(intro) = intro else {
            panic!("source did not select the use continuation");
        };
        let declaration = commit_use_declaration(&mut committed, intro)
            .expect("use continuation should parse the source");
        (declaration, committed.into_output())
    }

    fn parse_direct_binding_with_output<'source>(
        source: &'source str,
        operators: &crate::operator::OperatorTable,
    ) -> (ParsedBindingDeclaration<'source, rowan::Checkpoint>, FullCstOutput<'source>) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let mut probe = Probe::new(i);
        let intro = probe
            .input()
            .run(recognize_binding_statement_intro)
            .expect("binding prefix");
        let mut committed = probe.commit(FullCstOutput::new(source));
        let declaration = commit_binding_declaration(operators, &mut committed, intro)
            .expect("complete binding declaration");
        (declaration, committed.into_output())
    }

    fn parse_direct_header_with_output<'source, O>(
        source: &'source str,
        output: O,
    ) -> (HeaderDeclaration<'source>, O)
    where
        O: CommitOutput<'source>,
    {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        parse_direct_header_declaration(Probe::new(i), output)
            .expect("source has a direct header declaration")
    }

    #[test]
    fn statement_intro_is_sink_free_and_rolls_back_a_failed_prefix() {
        let source = "pub neither";
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let calls = Rc::new(RefCell::new(Vec::new()));

        assert!(commit_header_statement(
            Probe::new(i),
            RecordingOutput {
                calls: Rc::clone(&calls),
            },
        )
        .is_none());
        assert!(calls.borrow().is_empty());
        assert_eq!(source_input.remainder(), source);
    }

    #[test]
    fn statement_intro_selects_use_and_operator_continuations_without_emitting() {
        for (source, expected_remainder) in [
            ("our use std", "std"),
            ("pub lazy infix (<+>)", "(<+>)"),
        ] {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            let mut expectations = chasa::LatestSink::new();
            let mut is_cut = false;
            let i = In::new(
                &mut source_input,
                &mut expectations,
                IsCut::new(&mut is_cut),
            )
            .set_local(&mut local);
            let calls = Rc::new(RefCell::new(Vec::new()));
            let (intro, mut committed) = commit_header_statement(
                Probe::new(i),
                RecordingOutput {
                    calls: Rc::clone(&calls),
                },
            )
            .expect("source has a header statement introduction");

            match (source, intro) {
                ("our use std", HeaderStatementIntro::Use(intro)) => {
                    assert_eq!(intro.start, 0);
                    assert_eq!(intro.visibility.unwrap().visibility, Visibility::Our);
                    assert_eq!(intro.use_keyword.text(), "use");
                }
                ("pub lazy infix (<+>)", HeaderStatementIntro::Operator(intro)) => {
                    assert_eq!(intro.start, 0);
                    assert_eq!(intro.visibility.unwrap().visibility, Visibility::Public);
                    assert_eq!(intro.lazy_keyword.map(|word| word.text()), Some("lazy"));
                    assert_eq!(intro.fixity, OperatorFixity::Infix);
                }
                _ => panic!("unexpected introduction for {source}"),
            }
            committed.probe(|probe| {
                assert_eq!(probe.input().input.remainder(), expected_remainder);
            });
            assert!(calls.borrow().is_empty());
        }
    }

    #[test]
    fn shared_statement_intro_gives_my_name_equals_priority_over_header_spellings() {
        for source in ["my use = value", "my lazy = value", "my infix = value"] {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            let mut expectations = chasa::LatestSink::new();
            let mut is_cut = false;
            let mut i = In::new(
                &mut source_input,
                &mut expectations,
                IsCut::new(&mut is_cut),
            )
            .set_local(&mut local);

            assert!(matches!(
                i.run(recognize_statement_intro),
                Some(StatementIntro::Binding(_))
            ));
            assert_eq!(source_input.remainder(), &source[2..]);
        }

        let source = "my use std";
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        assert!(matches!(
            i.run(recognize_statement_intro),
            Some(StatementIntro::Use(_))
        ));
    }

    #[test]
    fn direct_binding_declaration_emits_one_operator_aware_value_subtree() {
        let source = "my value = +!result";
        let operators = crate::operator::OperatorTable::from_declarations([
            crate::operator::OperatorDeclaration::new(
                "+!",
                crate::operator::OperatorFixities::new()
                    .with_prefix(crate::operator::BindingPower::scalar(70)),
            ),
        ])
        .expect("operator table");
        let (binding, output) = parse_direct_binding_with_output(source, &operators);
        let root = SyntaxNode::new_root(output.finish_complete());

        assert_eq!(binding.range(), 0..source.len());
        assert_eq!(binding.name().text(), "value");
        assert_eq!(binding.value().range(), 11..19);
        assert_eq!(root.kind(), SyntaxKind::BindingStatement);
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.children()
                .filter_map(|node| (node.kind() == SyntaxKind::PrefixExpression).then_some(node))
                .count(),
            1
        );
    }

    #[test]
    fn direct_operator_header_has_header_full_fact_parity_and_canonical_shape() {
        let source = "pub lazy infix (<+>) 5.0 5.1 =";
        let (header_declaration, _) =
            parse_direct_operator_with_output(source, HeaderOutput::new());
        let (full_declaration, full_output) =
            parse_direct_operator_with_output(source, FullCstOutput::new(source));

        assert_eq!(header_declaration, full_declaration);
        assert_eq!(full_output.finish_complete().to_string(), source);

        let (_, full_output) = parse_direct_operator_with_output(source, FullCstOutput::new(source));
        let root = SyntaxNode::new_root(full_output.finish_complete());
        let tokens = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>();
        assert_eq!(
            tokens,
            [
                (SyntaxKind::PubKw, "pub".to_owned()),
                (SyntaxKind::Whitespace, " ".to_owned()),
                (SyntaxKind::LazyKw, "lazy".to_owned()),
                (SyntaxKind::Whitespace, " ".to_owned()),
                (SyntaxKind::InfixKw, "infix".to_owned()),
                (SyntaxKind::Whitespace, " ".to_owned()),
                (SyntaxKind::LParen, "(".to_owned()),
                (SyntaxKind::Operator, "<+>".to_owned()),
                (SyntaxKind::RParen, ")".to_owned()),
                (SyntaxKind::Whitespace, " ".to_owned()),
                (SyntaxKind::Integer, "5".to_owned()),
                (SyntaxKind::Dot, ".".to_owned()),
                (SyntaxKind::Integer, "0".to_owned()),
                (SyntaxKind::Whitespace, " ".to_owned()),
                (SyntaxKind::Integer, "5".to_owned()),
                (SyntaxKind::Dot, ".".to_owned()),
                (SyntaxKind::Integer, "1".to_owned()),
                (SyntaxKind::Whitespace, " ".to_owned()),
                (SyntaxKind::Equals, "=".to_owned()),
            ]
        );
        assert_eq!(root.kind(), SyntaxKind::OperatorHeader);
    }

    #[test]
    fn direct_operator_header_preserves_each_fixitys_binding_power_arity() {
        let cases = [
            ("nullfix (+) =", None, None),
            ("prefix (+) 1.2 =", None, Some(&[1, 2][..])),
            ("suffix (+) 3.4 =", Some(&[3, 4][..]), None),
            ("infix (+) 5.6 7.8 =", Some(&[5, 6][..]), Some(&[7, 8][..])),
        ];

        for (source, left, right) in cases {
            let (declaration, output) =
                parse_direct_operator_with_output(source, FullCstOutput::new(source));
            assert_eq!(
                declaration.left_binding_power().map(BindingPower::components),
                left,
                "{source}"
            );
            assert_eq!(
                declaration.right_binding_power().map(BindingPower::components),
                right,
                "{source}"
            );
            assert_eq!(output.finish_complete().to_string(), source, "{source}");
        }
    }

    #[test]
    fn direct_use_declaration_has_header_full_fact_parity_and_lossless_groups() {
        for source in [
            "use {read, write}",
            "use std::io::{read, write}",
            "use std::{io::{read},\nwrite,}",
            "use std::io::{}",
            "use (+)::value",
            "use realm/{tools}",
            "use band::*",
        ] {
            let (header_declaration, _) =
                parse_direct_use_with_output(source, HeaderOutput::new());
            let (full_declaration, full_output) =
                parse_direct_use_with_output(source, FullCstOutput::new(source));
            assert_eq!(header_declaration, full_declaration, "{source}");
            assert_eq!(full_output.finish_complete().to_string(), source, "{source}");
        }
    }

    #[test]
    fn direct_use_glob_keeps_alias_without_and_qualifier_tokens_losslessly() {
        let source = "use std::* as all as every without {foo, (*)} v1 with program::ui";
        let (declaration, output) = parse_direct_use_with_output(source, FullCstOutput::new(source));
        let root = SyntaxNode::new_root(output.finish_complete());

        assert_eq!(root.kind(), SyntaxKind::UseDeclaration);
        assert_eq!(root.to_string(), source);
        assert_eq!(
            declaration
                .tree()
                .qualifiers()
                .version()
                .map(UseVersion::text),
            Some("v1")
        );
        assert_eq!(
            path_texts(
                declaration
                    .tree()
                    .qualifiers()
                    .anchor()
                    .expect("anchor should parse")
            ),
            ["program", "ui"]
        );
        assert!(matches!(
            glob_parts(declaration.tree()).1,
            [UseExclusion::Group { .. }]
        ));
        assert_eq!(
            declaration
                .tree()
                .aliases()
                .iter()
                .map(|alias| alias.text())
                .collect::<Vec<_>>(),
            ["all", "every"]
        );
    }

    #[test]
    fn shared_direct_statement_dispatch_returns_the_same_header_facts_in_both_modes() {
        for source in ["our use std::io", "pub lazy infix (<+>) 5.0 5.1 ="] {
            let (header, _) = parse_direct_header_with_output(source, HeaderOutput::new());
            let (full, output) =
                parse_direct_header_with_output(source, FullCstOutput::new(source));
            assert_eq!(header, full, "{source}");
            assert_eq!(output.finish_complete().to_string(), source, "{source}");
        }
    }

    #[test]
    fn parses_scalar_and_vector_operator_binding_powers() {
        for (source, expected) in [("50", &[50][..]), ("5.0.1", &[5, 0, 1][..])] {
            let (binding_power, remainder) = parse_operator_binding_power(source);

            assert_eq!(binding_power.components(), expected, "{source}");
            assert_eq!(remainder, "", "{source}");
        }
    }

    #[test]
    fn parses_every_operator_header_fixity_with_its_binding_power_shape() {
        let cases = [
            ("nullfix (+) = body", OperatorFixity::Nullfix, None, None),
            (
                "prefix (not) 7.0 = body",
                OperatorFixity::Prefix,
                None,
                Some(&[7, 0][..]),
            ),
            (
                "suffix (!) 8 = body",
                OperatorFixity::Suffix,
                Some(&[8][..]),
                None,
            ),
            (
                "infix (+) 5.0.0 5.0.1 = body",
                OperatorFixity::Infix,
                Some(&[5, 0, 0][..]),
                Some(&[5, 0, 1][..]),
            ),
        ];

        for (source, fixity, left, right) in cases {
            let (header, remainder) = parse_operator_header_declaration(source);

            assert_eq!(header.fixity(), fixity, "{source}");
            assert_eq!(
                header.left_binding_power().map(BindingPower::components),
                left,
                "{source}"
            );
            assert_eq!(
                header.right_binding_power().map(BindingPower::components),
                right,
                "{source}"
            );
            assert_eq!(remainder, " body", "{source}");
        }
    }

    #[test]
    fn parses_operator_header_visibility_and_lazy_modifier() {
        let (public, public_remainder) =
            parse_operator_header_declaration("pub lazy infix(and) 2.0.0 2.0.1 = body");
        let (private, private_remainder) =
            parse_operator_header_declaration("my prefix (-) 8 = body");
        let (our, our_remainder) = parse_operator_header_declaration("our suffix (!) 8 = body");

        assert_eq!(public.visibility(), Visibility::Public);
        assert!(public.is_lazy());
        assert_eq!(private.visibility(), Visibility::Private);
        assert!(!private.is_lazy());
        assert_eq!(our.visibility(), Visibility::Our);
        assert_eq!(public_remainder, " body");
        assert_eq!(private_remainder, " body");
        assert_eq!(our_remainder, " body");

        let projected = public.to_header_operator();
        assert_eq!(projected.range(), &(0..33));
        assert_eq!(projected.name(), "and");
        assert_eq!(projected.visibility(), Visibility::Public);
        assert!(projected.is_lazy());
        assert_eq!(
            projected
                .binding_power()
                .right()
                .map(HeaderBindingPower::components),
            Some(&[2, 0, 1][..])
        );
    }

    #[test]
    fn classifies_all_leading_use_fixtures() {
        let cases = [
            (
                LEADING_USE_SOURCE,
                HeaderImportForm::Plain,
                0..13,
                &["std", "data"] as &[_],
            ),
            (
                LEADING_MOD_USE_SOURCE,
                HeaderImportForm::Mod,
                0..19,
                &["math", "value"],
            ),
            (
                LEADING_REALM_USE_SOURCE,
                HeaderImportForm::Realm,
                0..23,
                &["tools", "format"],
            ),
            (
                LEADING_BAND_USE_SOURCE,
                HeaderImportForm::Band,
                0..24,
                &["support", "value"],
            ),
        ];

        for (bytes, form, range, path) in cases {
            let source = std::str::from_utf8(bytes).expect("fixture is UTF-8");
            let (declaration, remainder) = parse_use(source);

            assert_eq!(declaration.range(), range, "{source:?}");
            assert_eq!(declaration.visibility(), Visibility::Private, "{source:?}");
            assert_eq!(declaration.tree().form(), form, "{source:?}");
            assert_eq!(path_texts(declaration.tree().prefix()), path, "{source:?}");
            assert_eq!(remainder, "\nmy value = 1\n", "{source:?}");

            let import = declaration
                .project_single_import()
                .expect("fixture use declaration should project");
            assert_eq!(import.range(), &range, "{source:?}");
            assert_eq!(import.form(), form, "{source:?}");
            assert_eq!(import.path(), path, "{source:?}");
            assert_eq!(import.visibility(), Visibility::Private, "{source:?}");
            assert_eq!(import.alias(), None, "{source:?}");
        }
    }

    #[test]
    fn keeps_non_marker_paths_plain() {
        let cases = [
            (
                "use realm::x",
                &["realm", "x"] as &[_],
                &[UseSeparator::ColonColon][..],
            ),
            ("use band/x", &["band", "x"], &[UseSeparator::Slash][..]),
            (
                "use a/b::c",
                &["a", "b", "c"],
                &[UseSeparator::Slash, UseSeparator::ColonColon][..],
            ),
        ];

        for (source, path, separators) in cases {
            let (declaration, remainder) = parse_use(source);

            assert_eq!(
                declaration.tree().form(),
                HeaderImportForm::Plain,
                "{source}"
            );
            assert_eq!(path_texts(declaration.tree().prefix()), path, "{source}");
            assert_eq!(
                declaration.tree().prefix().separators(),
                separators,
                "{source}"
            );
            assert_eq!(remainder, "", "{source}");
        }
    }

    #[test]
    fn projects_a_single_explicit_alias() {
        let (declaration, remainder) = parse_use("use std::data as collection");
        let import = declaration
            .project_single_import()
            .expect("one alias should project");

        assert_eq!(import.range(), &(0..27));
        assert_eq!(import.path(), ["std", "data"]);
        assert_eq!(import.alias(), Some("collection"));
        assert_eq!(remainder, "");
    }

    #[test]
    fn projects_operator_segments_by_their_canonical_spelling() {
        let declaration = UseDeclaration {
            range: 0..8,
            visibility: Visibility::Private,
            tree: UseTree {
                range: 4..8,
                form: HeaderImportForm::Plain,
                prefix: UsePath {
                    segments: vec![UseSegment::Operator {
                        range: 5..7,
                        text: "+!",
                    }],
                    separators: Vec::new(),
                },
                terminal: UseTerminal::Single,
                aliases: Vec::new(),
                qualifiers: UseQualifiers::default(),
            },
        };

        let import = declaration
            .project_single_import()
            .expect("single operator segment should project");

        assert_eq!(import.path(), ["+!"]);
        assert!(import.route().separators().is_empty());
    }

    #[test]
    fn preserves_distinct_plain_routes_during_projection() {
        let (slash, _) = parse_use("use a/b::c");
        let (colon_colon, _) = parse_use("use a::b::c");
        let slash = slash
            .project_single_import()
            .expect("slash route should project");
        let colon_colon = colon_colon
            .project_single_import()
            .expect("double-colon route should project");

        assert_eq!(slash.path(), colon_colon.path());
        assert_eq!(
            slash.route().separators(),
            [
                HeaderImportRouteSeparator::Slash,
                HeaderImportRouteSeparator::ColonColon,
            ]
        );
        assert_eq!(
            colon_colon.route().separators(),
            [
                HeaderImportRouteSeparator::ColonColon,
                HeaderImportRouteSeparator::ColonColon,
            ]
        );
        assert_ne!(slash.route(), colon_colon.route());
    }

    #[test]
    fn parses_a_glob_only_after_a_path_separator() {
        let (declaration, remainder) = parse_use("use std::*");

        assert_eq!(path_texts(declaration.tree().prefix()), ["std"]);
        let (join, without) = glob_parts(declaration.tree());
        assert_eq!(join, Some(UseSeparator::ColonColon));
        assert!(without.is_empty());
        assert_eq!(remainder, "");
        assert!(!parses_declaration("use *"));
    }

    #[test]
    fn parses_name_and_glob_exclusions_after_without() {
        let (name_declaration, _) = parse_use("use std::* without foo");
        let (_, name_without) = glob_parts(name_declaration.tree());
        assert_eq!(name_without.len(), 1);
        assert_eq!(exclusion_segment_text(&name_without[0]), Some("foo"));

        let (glob_declaration, _) = parse_use("use std::* without *");
        let (_, glob_without) = glob_parts(glob_declaration.tree());
        assert_eq!(glob_without.len(), 1);
        assert!(matches!(glob_without[0], UseExclusion::Glob { .. }));
    }

    #[test]
    fn retains_glob_aliases_before_parsing_without() {
        let (declaration, _) = parse_use("use std::* as all without foo");
        let (_, without) = glob_parts(declaration.tree());

        assert_eq!(
            declaration
                .tree()
                .aliases()
                .iter()
                .map(|alias| alias.text())
                .collect::<Vec<_>>(),
            ["all"]
        );
        assert_eq!(exclusion_segment_text(&without[0]), Some("foo"));
    }

    #[test]
    fn parses_parenthesized_exclusion_groups() {
        let (declaration, _) = parse_use("use std::* without (a, b)");
        let (_, without) = glob_parts(declaration.tree());

        let [UseExclusion::Group { items, .. }] = without else {
            panic!("expected one parenthesized exclusion group: {without:#?}");
        };
        assert_eq!(items.len(), 2);
        assert_eq!(path_texts(items[0].prefix()), ["a"]);
        assert_eq!(path_texts(items[1].prefix()), ["b"]);
    }

    #[test]
    fn parses_brace_exclusion_groups() {
        let (declaration, _) = parse_use("use std::* without {a, b}");
        let (_, without) = glob_parts(declaration.tree());

        let [UseExclusion::Group { items, .. }] = without else {
            panic!("expected one brace exclusion group: {without:#?}");
        };
        assert_eq!(
            items
                .iter()
                .map(|item| path_texts(item.prefix()))
                .collect::<Vec<_>>(),
            [vec!["a"], vec!["b"]]
        );
    }

    #[test]
    fn keeps_parenthesized_operator_names_distinct_from_glob_exclusions() {
        let (declaration, _) = parse_use("use std::* without (*)");
        let (_, without) = glob_parts(declaration.tree());

        let [UseExclusion::Segment(UseSegment::Operator { text, .. })] = without else {
            panic!("expected parenthesized star to remain an operator segment: {without:#?}");
        };
        assert_eq!(*text, "*");
    }

    #[test]
    fn accepts_parenthesized_operator_segments_at_normal_path_positions() {
        let (at_spec_start, remainder) = parse_use("use (+)::value");
        assert_eq!(remainder, "");
        let [
            UseSegment::Operator { range, text },
            UseSegment::Word(word),
        ] = at_spec_start.tree().prefix().segments()
        else {
            panic!("expected an operator followed by a word path segment");
        };
        assert_eq!(range, &(4..7));
        assert_eq!(*text, "+");
        assert_eq!(word.text(), "value");

        let (at_separator_target, remainder) = parse_use("use std::(+)::value");
        assert_eq!(remainder, "");
        assert_eq!(
            path_texts(at_separator_target.tree().prefix()),
            ["std", "+", "value"]
        );
        assert_eq!(
            at_separator_target.tree().prefix().separators(),
            [UseSeparator::ColonColon, UseSeparator::ColonColon]
        );
    }

    #[test]
    fn parses_a_typed_version_suffix() {
        let (declaration, remainder) = parse_use("use std::data v1.2.3");
        let qualifiers = declaration.tree().qualifiers();
        let version = qualifiers.version().expect("version suffix should parse");

        assert_eq!(version.text(), "v1.2.3");
        assert_eq!(version.range(), 14..20);
        assert!(qualifiers.anchor().is_none());
        assert_eq!(declaration.range(), 0..20);
        assert_eq!(remainder, "");
        assert_eq!(
            declaration.project_single_import(),
            Err(UseSingleProjectionError::Qualifiers)
        );
        assert!(matches!(
            declaration.expand_header_imports().as_slice(),
            [Err(UseExpansionError::Qualifiers { .. })]
        ));
    }

    #[test]
    fn preserves_the_full_version_token_spelling() {
        let (declaration, _) = parse_use("use std::data v1-alpha+build.2");

        assert_eq!(
            declaration
                .tree()
                .qualifiers()
                .version()
                .map(UseVersion::text),
            Some("v1-alpha+build.2")
        );
    }

    #[test]
    fn parses_an_identifier_path_anchor() {
        let (declaration, remainder) = parse_use("use std::data with program::ui");
        let qualifiers = declaration.tree().qualifiers();
        let anchor = qualifiers.anchor().expect("anchor should parse");

        assert!(qualifiers.version().is_none());
        assert_eq!(path_texts(anchor), ["program", "ui"]);
        assert_eq!(anchor.separators(), [UseSeparator::ColonColon]);
        assert_eq!(declaration.range(), 0..30);
        assert_eq!(remainder, "");
    }

    #[test]
    fn parses_version_then_anchor_in_source_order() {
        let (declaration, remainder) = parse_use("use std::data v1.2.3 with program::ui");
        let qualifiers = declaration.tree().qualifiers();

        assert_eq!(qualifiers.version().map(UseVersion::text), Some("v1.2.3"));
        assert_eq!(
            path_texts(qualifiers.anchor().expect("anchor should parse")),
            ["program", "ui"]
        );
        assert_eq!(declaration.range(), 0..37);
        assert_eq!(remainder, "");
    }

    #[test]
    fn parses_qualifiers_on_group_items_and_glob_tails() {
        let (group, _) = parse_use("use std::{read v1, write with program::ui}");
        let (_, items) = group_parts(group.tree());
        assert_eq!(
            items[0].qualifiers().version().map(UseVersion::text),
            Some("v1")
        );
        assert_eq!(
            path_texts(items[1].qualifiers().anchor().expect("anchor should parse")),
            ["program", "ui"]
        );
        assert_eq!(items[0].range(), 10..17);
        assert_eq!(items[1].range(), 19..41);

        let (glob, _) = parse_use("use std::* without foo v1.2.3 with program::ui");
        let (_, without) = glob_parts(glob.tree());
        assert_eq!(exclusion_segment_text(&without[0]), Some("foo"));
        assert_eq!(
            glob.tree().qualifiers().version().map(UseVersion::text),
            Some("v1.2.3")
        );
        assert_eq!(
            path_texts(
                glob.tree()
                    .qualifiers()
                    .anchor()
                    .expect("anchor should parse")
            ),
            ["program", "ui"]
        );
    }

    #[test]
    fn rejects_non_identifier_anchor_targets() {
        for source in [
            "use std::data with {program}",
            "use std::data with *",
            "use std::data with (*)",
        ] {
            assert!(!parses_declaration(source), "{source}");
        }
    }

    #[test]
    fn expands_a_common_prefix_group_into_independent_imports() {
        let (declaration, remainder) = parse_use("use std::io::{read, write}");
        let imports = complete_expansions(&declaration);

        assert_eq!(imports.len(), 2);
        assert_eq!(imports[0].range(), &(14..18));
        assert_eq!(imports[1].range(), &(20..25));
        assert_eq!(imports[0].path(), ["std", "io", "read"]);
        assert_eq!(imports[1].path(), ["std", "io", "write"]);
        assert!(imports.iter().all(|import| {
            import.route().separators()
                == [
                    HeaderImportRouteSeparator::ColonColon,
                    HeaderImportRouteSeparator::ColonColon,
                ]
        }));
        assert!(imports.iter().all(|import| import.alias().is_none()));
        assert!(
            imports
                .iter()
                .all(|import| import.visibility() == Visibility::Private)
        );
        assert_eq!(remainder, "");
    }

    #[test]
    fn expands_nested_groups_in_depth_first_source_order() {
        let (declaration, _) = parse_use("use std::{io::{read, write}, fs}");
        let imports = complete_expansions(&declaration);

        assert_eq!(
            imports.iter().map(HeaderImport::path).collect::<Vec<_>>(),
            [
                &["std".to_owned(), "io".to_owned(), "read".to_owned()][..],
                &["std".to_owned(), "io".to_owned(), "write".to_owned()][..],
                &["std".to_owned(), "fs".to_owned()][..],
            ]
        );
    }

    #[test]
    fn does_not_emit_records_for_an_empty_group() {
        let (declaration, remainder) = parse_use("use std::io::{}");

        assert!(declaration.expand_header_imports().is_empty());
        assert_eq!(remainder, "");
    }

    #[test]
    fn keeps_complete_siblings_when_one_group_item_has_a_form_conflict() {
        let (declaration, _) = parse_use("use std::{realm/tools, plain}");
        let results = declaration.expand_header_imports();

        assert!(matches!(
            results[0],
            Err(UseExpansionError::FormConflict {
                inherited_form: HeaderImportForm::Plain,
                form: HeaderImportForm::Realm,
                ..
            })
        ));
        let import = results[1]
            .as_ref()
            .expect("the complete sibling should still expand");
        assert_eq!(import.path(), ["std", "plain"]);
        assert_eq!(import.form(), HeaderImportForm::Plain);
    }

    #[test]
    fn rejects_an_alias_on_a_group_without_expanding_its_children() {
        let (declaration, _) = parse_use("use std::{read} as selected");

        assert_eq!(
            declaration.expand_header_imports(),
            vec![Err(UseExpansionError::GroupAlias { range: 4..27 })]
        );
    }

    #[test]
    fn rejects_repeated_aliases_on_a_single_branch() {
        let (declaration, _) = parse_use("use std::data as first as second");

        assert_eq!(
            declaration.expand_header_imports(),
            vec![Err(UseExpansionError::MultipleAliases { range: 4..32 })]
        );
    }

    #[test]
    fn keeps_complete_siblings_when_a_recovered_item_has_no_target() {
        let (mut declaration, _) = parse_use("use {missing, complete}");
        let UseTerminal::Group { items, .. } = &mut declaration.tree.terminal else {
            panic!("expected root group");
        };
        items[0].prefix = empty_use_path();

        let results = declaration.expand_header_imports();

        assert!(matches!(
            results[0],
            Err(UseExpansionError::MissingTarget { .. })
        ));
        assert_eq!(
            results[1]
                .as_ref()
                .expect("complete sibling should still expand")
                .path(),
            ["complete"]
        );
    }

    #[test]
    fn keeps_complete_siblings_when_a_group_item_is_a_glob() {
        let (mut declaration, _) = parse_use("use std::{glob, complete}");
        let UseTerminal::Group { items, .. } = &mut declaration.tree.terminal else {
            panic!("expected group terminal");
        };
        items[0].terminal = UseTerminal::Glob {
            join: None,
            without: Vec::new(),
        };

        let results = declaration.expand_header_imports();

        assert!(matches!(
            results[0],
            Err(UseExpansionError::UnsupportedGlob { .. })
        ));
        assert_eq!(
            results[1]
                .as_ref()
                .expect("complete sibling should still expand")
                .path(),
            ["std", "complete"]
        );
    }

    #[test]
    fn parses_a_simple_group_after_a_common_prefix() {
        let (declaration, remainder) = parse_use("use std::io::{read, write}");

        assert_eq!(path_texts(declaration.tree().prefix()), ["std", "io"]);
        assert_eq!(
            declaration.tree().prefix().separators(),
            [UseSeparator::ColonColon]
        );
        assert_eq!(remainder, "");

        let (join, items) = group_parts(declaration.tree());
        assert_eq!(join, Some(UseSeparator::ColonColon));
        assert_eq!(items.len(), 2);
        assert_eq!(path_texts(items[0].prefix()), ["read"]);
        assert_eq!(path_texts(items[1].prefix()), ["write"]);
        assert!(matches!(items[0].terminal(), UseTerminal::Single));
        assert!(matches!(items[1].terminal(), UseTerminal::Single));
    }

    #[test]
    fn parses_nested_groups_in_source_order() {
        let (declaration, remainder) = parse_use("use std::{io::{read, write}, fs}");

        let (_, outer_items) = group_parts(declaration.tree());
        assert_eq!(outer_items.len(), 2);
        assert_eq!(path_texts(outer_items[0].prefix()), ["io"]);
        assert_eq!(path_texts(outer_items[1].prefix()), ["fs"]);

        let (join, inner_items) = group_parts(&outer_items[0]);
        assert_eq!(join, Some(UseSeparator::ColonColon));
        assert_eq!(
            inner_items
                .iter()
                .map(|item| path_texts(item.prefix()))
                .collect::<Vec<_>>(),
            [vec!["read"], vec!["write"]]
        );
        assert_eq!(remainder, "");
    }

    #[test]
    fn accepts_newlines_as_group_item_separators() {
        let (declaration, remainder) = parse_use("use std::{\n  read\n  write,\n}");

        let (_, items) = group_parts(declaration.tree());
        assert_eq!(items.len(), 2);
        assert_eq!(path_texts(items[0].prefix()), ["read"]);
        assert_eq!(path_texts(items[1].prefix()), ["write"]);
        assert_eq!(remainder, "");
    }

    #[test]
    fn root_group_items_classify_their_own_forms() {
        let (declaration, remainder) = parse_use("use {mod math, realm/tools, band::support, std}");

        assert!(declaration.tree().prefix().segments().is_empty());
        let (_, items) = group_parts(declaration.tree());
        assert_eq!(
            items.iter().map(UseTree::form).collect::<Vec<_>>(),
            [
                HeaderImportForm::Mod,
                HeaderImportForm::Realm,
                HeaderImportForm::Band,
                HeaderImportForm::Plain,
            ]
        );
        assert_eq!(path_texts(items[0].prefix()), ["math"]);
        assert_eq!(path_texts(items[1].prefix()), ["tools"]);
        assert_eq!(path_texts(items[2].prefix()), ["support"]);
        assert_eq!(path_texts(items[3].prefix()), ["std"]);
        assert_eq!(remainder, "");
    }

    #[test]
    fn retains_every_alias_and_its_range() {
        let source = "use std::io::{read as one as two}";
        let (declaration, remainder) = parse_use(source);

        let (_, items) = group_parts(declaration.tree());
        assert_eq!(items.len(), 1);
        assert_eq!(
            items[0]
                .aliases()
                .iter()
                .map(|alias| alias.text())
                .collect::<Vec<_>>(),
            ["one", "two"]
        );
        assert_eq!(
            items[0]
                .aliases()
                .iter()
                .map(|alias| alias.range())
                .collect::<Vec<_>>(),
            [22..25, 29..32]
        );
        assert_eq!(remainder, "");
    }

    fn parse_use(source: &str) -> (UseDeclaration<'_>, &str) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let declaration = i
            .run(parse_declaration)
            .expect("leading use declaration should parse");

        let Declaration::Use(declaration) = declaration else {
            panic!("expected use declaration");
        };
        (declaration, i.input.remainder())
    }

    fn parse_operator_binding_power(source: &str) -> (BindingPower, &str) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let binding_power = i
            .run(parse_binding_power)
            .expect("operator binding power should parse");
        (binding_power, i.input.remainder())
    }

    fn parse_operator_header_declaration(source: &str) -> (OperatorHeaderDeclaration<'_>, &str) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let declaration = i
            .run(parse_declaration)
            .expect("operator header should parse");
        let Declaration::OperatorHeader(header) = declaration else {
            panic!("expected operator header");
        };
        (header, i.input.remainder())
    }

    fn path_texts<'source>(path: &UsePath<'source>) -> Vec<&'source str> {
        path.segments()
            .iter()
            .map(|segment| match segment {
                UseSegment::Word(word) => word.text(),
                UseSegment::Operator { text, .. } => *text,
            })
            .collect()
    }

    fn group_parts<'tree, 'source>(
        tree: &'tree UseTree<'source>,
    ) -> (Option<UseSeparator>, &'tree [UseTree<'source>]) {
        let UseTerminal::Group { join, items } = tree.terminal() else {
            panic!("expected use group terminal: {tree:#?}");
        };
        (*join, items)
    }

    fn glob_parts<'tree, 'source>(
        tree: &'tree UseTree<'source>,
    ) -> (Option<UseSeparator>, &'tree [UseExclusion<'source>]) {
        let UseTerminal::Glob { join, without } = tree.terminal() else {
            panic!("expected use glob terminal: {tree:#?}");
        };
        (*join, without)
    }

    fn exclusion_segment_text<'source>(exclusion: &UseExclusion<'source>) -> Option<&'source str> {
        let UseExclusion::Segment(UseSegment::Word(word)) = exclusion else {
            return None;
        };
        Some(word.text())
    }

    fn parses_declaration(source: &str) -> bool {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        i.run(parse_declaration).is_some()
    }

    fn complete_expansions(declaration: &UseDeclaration<'_>) -> Vec<HeaderImport> {
        declaration
            .expand_header_imports()
            .into_iter()
            .collect::<Result<Vec<_>, _>>()
            .expect("all tested branches should expand")
    }

    #[test]
    fn parses_binding_with_minimal_expression_from_chasa_input() {
        let source = "my value = 123\n";
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let declaration = i
            .run(parse_declaration)
            .expect("binding declaration should parse");

        let Declaration::Binding(binding) = declaration else {
            panic!("expected binding declaration");
        };
        assert_eq!(binding.range(), 0..14);
        assert_eq!(binding.name().text(), "value");
        assert_eq!(binding.value().range(), 11..14);
        assert_eq!(i.input.remainder(), "\n");
    }

    #[test]
    fn parses_infix_operator_header_fixture_from_chasa_input() {
        let source = std::str::from_utf8(INFIX_OPERATOR_SOURCE).expect("fixture is UTF-8");
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let declaration = i
            .run(parse_declaration)
            .expect("operator header should parse");

        let Declaration::OperatorHeader(header) = declaration else {
            panic!("expected operator header declaration");
        };
        assert_eq!(header.range(), 0..19);
        assert_eq!(header.name(), "<+>");
        assert_eq!(header.fixity(), OperatorFixity::Infix);
        assert_eq!(
            header.left_binding_power().map(BindingPower::components),
            Some(&[50][..])
        );
        assert_eq!(
            header.right_binding_power().map(BindingPower::components),
            Some(&[51][..])
        );
        assert_eq!(i.input.remainder(), " left\nmy value = 1\n");
    }
}

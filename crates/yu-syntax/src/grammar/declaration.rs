//! Shared grammar for source-leading declarations.

use std::{ops::Range, sync::Arc};

use chasa::{
    Back as _, ErrorSink, Input as _,
    error::std::{Unexpected, UnexpectedEndOfInput},
    input::IsCut,
    parser::Parser as _,
    prelude::{In, from_fn},
};

use crate::{
    BindingPower as HeaderBindingPower, BindingPowers, HeaderImport, HeaderImportForm,
    HeaderImportRoute, HeaderImportRouteSeparator, HeaderOperator, Visibility,
    grammar::expression::{
        IndentedStatementBlock, OperatorChain, ParsedExpression, commit_indented_binding_body,
        commit_indented_mod_body,
        Statement, BracedStatementBlockExpression, commit_braced_statement_block_expression,
        commit_canonical_statement, parse_braced_statement_block_expression,
        parse_direct_expression_with_operators, parse_expression_with_operators,
        parse_indented_binding_body, parse_indented_mod_body, parse_canonical_statement,
    },
    grammar::{
        pattern::{ParsedPattern, Pattern, parse_direct_pattern_with_outer_missing_role,
            parse_pattern_with_outer_missing_role},
        type_expr::{
            TypeExpression, commit_direct_type_expression_with_outer_missing_role,
            parse_required_type_expression_with_outer_missing_role, parse_type_expression,
        },
    },
    input::SourceInput,
    operator::{BindingPower, OperatorFixity},
    scan::{
        opaque_body::scan_root_recovery,
        operator::LeadingTrivia,
        punctuation::{PunctuationKind, scan_punctuation},
        trivia::{TriviaPartKind, TriviaRun, scan_trivia},
        word::{WordSpan, scan_path_segment, scan_word},
    },
    session::{
        BindingRole, CommitOutput, Committed, CommittedRecoveryRecord, ConstructRole,
        DeclarationRole, Delimiter, ExpectationSources, ExpectedSyntax, FullCstOutput, GrammarRole,
        ImportRole, IndentationBaseline, IndentationBaselineKind, LayoutDelimitedBoundary,
        LayoutDelimitedFrame, LayoutRole, OperatorHeaderRole, Probe, RecoveryKind, RecoverySiteKey,
        ModRole, RootUnexpected, RootUnexpectedHead, StatementKind, StatementRole, StopKind, SynIn,
        SyntaxExpectation, TypeDelimitedOwner, UnexpectedSyntax, any_ambient_owner_claims,
    },
    syntax_kind::SyntaxKind,
};

/// One parsed source-leading declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Declaration<'source> {
    Use(UseDeclaration<'source>),
    Binding(BindingDeclaration<'source>),
    OperatorHeader(OperatorHeaderDeclaration<'source>),
    Mod(ModDeclaration<'source>),
    Struct(StructDeclaration<'source>),
    Type(TypeDeclaration<'source>),
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
    Mod(ModStatementIntro<'source>),
    Struct(StructStatementIntro<'source>),
    Type(TypeStatementIntro<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UseStatementIntro<'source> {
    start: usize,
    visibility: Option<VisibilityPrefix<'source>>,
    after_visibility: Option<TriviaRun>,
    use_keyword: WordSpan<'source>,
    after_use: Option<TriviaRun>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OperatorStatementIntro<'source> {
    start: usize,
    visibility: Option<VisibilityPrefix<'source>>,
    lazy_keyword: Option<WordSpan<'source>>,
    after_visibility: Option<TriviaRun>,
    after_lazy: Option<TriviaRun>,
    /// A fixity recognized before commitment.  `lazy` deliberately leaves
    /// this slot to the continuation so a missing discriminator can recover.
    fixity_keyword: Option<WordSpan<'source>>,
    after_fixity: Option<TriviaRun>,
}

/// The committed prefix of a direct binding declaration.
///
/// The continuation owns the Pattern target and optional exact-equals body;
/// keeping both out of this sink-free prefix lets every statement owner cut at
/// the visibility word before recovery is selected.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BindingStatementIntro<'source> {
    start: usize,
    visibility: VisibilityPrefix<'source>,
}

/// The sink-free prefix shared by root and canonical-statement Mod parsing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ModStatementIntro<'source> {
    start: usize,
    visibility: Option<VisibilityPrefix<'source>>,
    after_visibility: Option<TriviaRun>,
    mod_keyword: WordSpan<'source>,
}

/// The sink-free prefix shared by root and canonical-statement Struct parsing.
///
/// `struct_base` is captured when the first accepted starter is still current;
/// later body parsing must not reconstruct it from the name or body opener.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StructStatementIntro<'source> {
    start: usize,
    visibility: Option<VisibilityPrefix<'source>>,
    after_visibility: Option<TriviaRun>,
    struct_keyword: WordSpan<'source>,
    struct_base: usize,
}

/// The sink-free prefix reserved for the shared Type-declaration judge.
///
/// Gate 1 only establishes this carrier; Gate 2 supplies the exact-word
/// recognition that fills it and commits the declaration authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypeStatementIntro<'source> {
    start: usize,
    visibility: Option<VisibilityPrefix<'source>>,
    after_visibility: Option<TriviaRun>,
    type_keyword: WordSpan<'source>,
    type_base: usize,
}

pub(crate) struct ParsedBindingDeclaration<'source, C> {
    visibility: Visibility,
    range: Range<usize>,
    target: Recovered<ParsedPattern<C>>,
    definition: Option<ParsedBindingDefinition<C>>,
    marker: std::marker::PhantomData<&'source str>,
}

pub(crate) struct ParsedBindingDefinition<C> {
    equals: Range<usize>,
    body: Recovered<ParsedBindingBody<C>>,
    range: Range<usize>,
}

pub(crate) struct ParsedBindingBody<C> {
    range: Range<usize>,
    marker: std::marker::PhantomData<C>,
}

/// A committed continuation completed its CST regardless of whether it could
/// produce the semantic value required by its caller.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Recovered<T> {
    Complete(T),
    Incomplete,
}

impl<'source, C> ParsedBindingDeclaration<'source, C> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn visibility(&self) -> Visibility {
        self.visibility
    }

    pub(crate) fn target(&self) -> &Recovered<ParsedPattern<C>> {
        &self.target
    }

    pub(crate) fn definition(&self) -> Option<&ParsedBindingDefinition<C>> {
        self.definition.as_ref()
    }
}

impl<C> ParsedBindingDefinition<C> {
    pub(crate) fn body(&self) -> &Recovered<ParsedBindingBody<C>> { &self.body }
    pub(crate) fn range(&self) -> Range<usize> { self.range.clone() }
}

impl<C> ParsedBindingBody<C> {
    fn new(range: Range<usize>) -> Self { Self { range, marker: std::marker::PhantomData } }
    pub(crate) fn range(&self) -> Range<usize> { self.range.clone() }
}

/// Builds the direct full-parse root candidate without changing `parse_file`.
///
/// The immutable operator table is supplied by the caller's session setup;
/// this candidate neither rebuilds it nor mutates it while parsing.
pub(crate) struct DirectRootCandidateOutput {
    green: rowan::GreenNode,
    committed_recoveries: Vec<CommittedRecoveryRecord>,
}

impl DirectRootCandidateOutput {
    pub(crate) fn green(&self) -> &rowan::GreenNode {
        &self.green
    }

    pub(crate) fn committed_recoveries(&self) -> &[CommittedRecoveryRecord] {
        &self.committed_recoveries
    }

    pub(crate) fn into_parts(self) -> (rowan::GreenNode, Vec<CommittedRecoveryRecord>) {
        (self.green, self.committed_recoveries)
    }
}

pub(crate) fn parse_direct_root_candidate(
    source: &str,
    operators: &crate::operator::OperatorTable,
    header_recoveries: &[CommittedRecoveryRecord],
) -> DirectRootCandidateOutput {
    let mut local = crate::session::ParseLocal::with_reusable_recoveries(header_recoveries);
    parse_direct_root_candidate_with_local(source, operators, &mut local)
}

fn parse_direct_root_candidate_with_local(
    source: &str,
    operators: &crate::operator::OperatorTable,
    local: &mut crate::session::ParseLocal,
) -> DirectRootCandidateOutput {
    let mut source_input = SourceInput::new(source);
    let mut expectations = chasa::LatestSink::new();
    let mut is_cut = false;
    let i = In::new(
        &mut source_input,
        &mut expectations,
        IsCut::new(&mut is_cut),
    )
    .set_local(local);
    let mut committed = Probe::new(i).commit(FullCstOutput::new(source));

    committed.start_node(SyntaxKind::Root);
    let ambient_scope = committed.probe(|probe| {
        probe.input().local.push_root_statement_ambient_scope()
    });
    let mut root_statement_start = true;
    let mut previous_statement = None;

    loop {
        let trivia = commit_trivia(&mut committed).expect("trivia scanning is total");
        if !trivia.is_empty() {
            root_statement_start |= trivia
                .parts()
                .iter()
                .any(|part| matches!(part.kind(), TriviaPartKind::Newline))
                && committed.probe(|probe| probe.input().local.line().line_indent == 0);
            committed.emit_trivia(&trivia);
        }

        if committed.probe(|probe| probe.input().input.remainder().is_empty()) {
            break;
        }

        if let Some(semicolon) = commit_character(&mut committed, ';') {
            committed.token(SyntaxKind::Semicolon, semicolon);
            root_statement_start = true;
            previous_statement = None;
            continue;
        }

        if !root_statement_start {
            emit_root_error(&mut committed, previous_statement);
            continue;
        }

        let intro = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let intro = i.run(recognize_statement_intro);
            if intro.is_none() {
                i.rollback(checkpoint);
            }
            intro
        });

        let Some(intro) = intro else {
            emit_root_error(&mut committed, None);
            continue;
        };

        previous_statement = Some(match intro {
            StatementIntro::Use(intro) => {
                let _ = commit_use_declaration(&mut committed, intro);
                StatementKind::UseDeclaration
            }
            StatementIntro::Binding(intro) => {
                let _ = commit_binding_declaration(operators, &mut committed, intro);
                StatementKind::BindingDeclaration
            }
            StatementIntro::Mod(intro) => {
                let _ = commit_mod_declaration(operators, &mut committed, intro);
                StatementKind::ModDeclaration
            }
            StatementIntro::Struct(intro) => {
                let _ = commit_struct_declaration(&mut committed, intro);
                StatementKind::StructDeclaration
            }
            StatementIntro::Type(intro) => {
                let _ = commit_type_declaration(&mut committed, intro);
                StatementKind::TypeDeclaration
            }
            StatementIntro::Operator(intro) => {
                if matches!(
                    commit_operator_header(&mut committed, intro),
                    Recovered::Complete(_)
                ) {
                    let _ = commit_operator_definition_body(operators, &mut committed);
                }
                StatementKind::OperatorDefinition
            }
        });
        root_statement_start = committed.probe(|probe| {
            let line = probe.input().local.line();
            line.at_line_start && line.line_indent == 0
        });
    }

    committed.probe(|probe| {
        assert_eq!(
            probe.input().local.pop_ambient_owner_scope(),
            Some(ambient_scope),
        );
    });
    committed.finish_node();
    let output = committed.into_output();
    let committed_recoveries = output.committed_recoveries().to_vec();
    DirectRootCandidateOutput {
        green: output.finish_complete(),
        committed_recoveries,
    }
}

fn emit_root_error<'parse, 'source, 'local, E>(
    committed: &mut Committed<'parse, 'source, 'local, E, FullCstOutput<'source>>,
    previous_statement: Option<StatementKind>,
) where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let range = committed.probe(|probe| {
        probe
            .input()
            .run(scan_root_recovery)
            .expect("root recovery always consumes a non-empty episode")
    });
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = previous_statement.map_or(StatementRole::Starter, |owner| {
            StatementRole::TrailingInput { owner }
        });
        let head = root_unexpected_head(i.input.source(), &range);
        let unexpected = previous_statement.map_or(
            RootUnexpected::UnrecognizedStarter {
                range: range.clone(),
                head,
            },
            |owner| RootUnexpected::TrailingInput {
                owner,
                range: range.clone(),
                head,
            },
        );
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role: GrammarRole::Statement(role),
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Root(unexpected)]),
            root_statement_expectations(role, range.clone()),
            0,
        )
    });
    committed.emit_error(record);
}

fn root_statement_expectations(
    role: StatementRole,
    range: Range<usize>,
) -> Arc<[SyntaxExpectation]> {
    Arc::from(
        [
            crate::session::KeywordEvidence::Use,
            crate::session::KeywordEvidence::Lazy,
            crate::session::KeywordEvidence::Prefix,
            crate::session::KeywordEvidence::Infix,
            crate::session::KeywordEvidence::Suffix,
            crate::session::KeywordEvidence::Nullfix,
        ]
        .map(|keyword| SyntaxExpectation {
            role: GrammarRole::Statement(role),
            expected: ExpectedSyntax::Keyword(keyword),
            range: range.clone(),
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }),
    )
}

fn root_unexpected_head(source: &str, range: &Range<usize>) -> RootUnexpectedHead {
    let remainder = &source[range.start..range.end];
    let character = remainder
        .chars()
        .next()
        .expect("root recovery ranges are non-empty");
    let punctuation = if remainder.starts_with("::") {
        Some(PunctuationKind::ColonColon)
    } else {
        match character {
            '(' => Some(PunctuationKind::Open(Delimiter::Parenthesis)),
            ')' => Some(PunctuationKind::Close(Delimiter::Parenthesis)),
            '[' => Some(PunctuationKind::Open(Delimiter::Bracket)),
            ']' => Some(PunctuationKind::Close(Delimiter::Bracket)),
            '{' => Some(PunctuationKind::Open(Delimiter::Brace)),
            '}' => Some(PunctuationKind::Close(Delimiter::Brace)),
            ',' => Some(PunctuationKind::Comma),
            ';' => Some(PunctuationKind::Semicolon),
            '.' => Some(PunctuationKind::Dot),
            '/' => Some(PunctuationKind::Slash),
            ':' => Some(PunctuationKind::Colon),
            '\\' => Some(PunctuationKind::Backslash),
            '\'' => Some(PunctuationKind::Apostrophe),
            _ => None,
        }
    };
    if let Some(punctuation) = punctuation {
        return RootUnexpectedHead::Punctuation(punctuation_evidence(punctuation));
    }
    match character {
        '_' => RootUnexpectedHead::Word,
        character if unicode_ident::is_xid_start(character) => RootUnexpectedHead::Word,
        character if character.is_ascii_digit() => RootUnexpectedHead::DecimalInteger,
        '=' => RootUnexpectedHead::Punctuation(crate::session::PunctuationEvidence::Equals),
        '*' => RootUnexpectedHead::Punctuation(crate::session::PunctuationEvidence::Star),
        '+' | '-' | '!' | '#' | '$' | '%' | '&' | '<' | '>' | '?' | '@' | '^' | '|' | '~' => {
            RootUnexpectedHead::OperatorLike
        }
        _ => RootUnexpectedHead::OtherCharacter,
    }
}

fn punctuation_evidence(kind: PunctuationKind) -> crate::session::PunctuationEvidence {
    match kind {
        PunctuationKind::Open(delimiter) => crate::session::PunctuationEvidence::Open(delimiter),
        PunctuationKind::Close(delimiter) => crate::session::PunctuationEvidence::Close(delimiter),
        PunctuationKind::Backslash => crate::session::PunctuationEvidence::Backslash,
        PunctuationKind::Apostrophe => crate::session::PunctuationEvidence::Apostrophe,
        PunctuationKind::Comma => crate::session::PunctuationEvidence::Comma,
        PunctuationKind::Semicolon => crate::session::PunctuationEvidence::Semicolon,
        PunctuationKind::Dot => crate::session::PunctuationEvidence::Dot,
        PunctuationKind::Slash => crate::session::PunctuationEvidence::Slash,
        PunctuationKind::ColonColon => crate::session::PunctuationEvidence::ColonColon,
        PunctuationKind::Colon => crate::session::PunctuationEvidence::Colon,
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
        StatementIntro::Mod(_) => {
            probe.input().rollback(checkpoint);
            return None;
        }
        StatementIntro::Struct(_) => {
            probe.input().rollback(checkpoint);
            return None;
        }
        StatementIntro::Type(_) => {
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
        HeaderStatementIntro::Use(intro) => match commit_use_declaration(&mut committed, intro) {
            Recovered::Complete(declaration) => HeaderDeclaration::Use(declaration),
            Recovered::Incomplete => return None,
        },
        HeaderStatementIntro::Operator(intro) => {
            match commit_operator_header(&mut committed, intro) {
                Recovered::Complete(declaration) => HeaderDeclaration::OperatorHeader(declaration),
                Recovered::Incomplete => return None,
            }
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
    if let Some(intro) = i.run(recognize_struct_statement_intro) {
        return Some(StatementIntro::Struct(intro));
    }

    if let Some(intro) = i.run(recognize_mod_statement_intro) {
        return Some(StatementIntro::Mod(intro));
    }

    if let Some(intro) = i.run(recognize_type_statement_intro) {
        return Some(StatementIntro::Type(intro));
    }

    if binding_statement_selected(&mut i) {
        return i
            .run(recognize_binding_statement_intro)
            .map(StatementIntro::Binding);
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
            // The committed continuation owns the mandatory separator and
            // first target, so a bare `use` is still a selected statement.
            after_use: scan_maybe_required_inline_trivia(&mut i),
        }));
    }

    if keyword.text() == "mod" {
        return Some(StatementIntro::Mod(ModStatementIntro {
            start,
            visibility,
            after_visibility,
            mod_keyword: keyword,
        }));
    }

    let (lazy_keyword, after_lazy, fixity_keyword) = if keyword.text() == "lazy" {
        // `lazy` alone is enough to select the committed operator
        // continuation.  Its required separator and fixity discriminator are
        // mandatory slots owned by that continuation.
        let after_lazy = scan_maybe_required_inline_trivia(&mut i);
        let fixity_keyword = after_lazy.as_ref().and_then(|_| {
            let checkpoint = i.checkpoint();
            let fixity_keyword = i
                .run(scan_word)
                .filter(|word| parse_operator_fixity(*word).is_some());
            if fixity_keyword.is_none() {
                i.rollback(checkpoint);
            }
            fixity_keyword
        });
        (Some(keyword), after_lazy, fixity_keyword)
    } else if parse_operator_fixity(keyword).is_some() {
        (None, None, Some(keyword))
    } else {
        return None;
    };

    let after_fixity = fixity_keyword
        .as_ref()
        .and_then(|_| scan_maybe_optional_inline_trivia(&mut i));

    Some(StatementIntro::Operator(OperatorStatementIntro {
        start,
        visibility,
        lazy_keyword,
        after_visibility,
        after_lazy,
        fixity_keyword,
        after_fixity,
    }))
}

fn recognize_struct_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<StructStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let struct_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first) {
        let Some(trivia) = mod_trivia(struct_base, &mut i) else {
            i.rollback(checkpoint);
            return None;
        };
        let Some(keyword) = i.run(scan_word) else {
            i.rollback(checkpoint);
            return None;
        };
        (Some(visibility), Some(trivia), keyword)
    } else {
        (None, None, first)
    };
    if keyword.text() != "struct" {
        i.rollback(checkpoint);
        return None;
    }
    Some(StructStatementIntro {
        start,
        visibility,
        after_visibility,
        struct_keyword: keyword,
        struct_base,
    })
}

/// Recognizes the sink-free prefix reserved for a Type declaration.
///
/// This remains deliberately separate from `recognize_statement_intro` until
/// the later dispatch gate.  An exact `type` keyword is enough to establish
/// declaration authority; all mandatory declaration slots belong to the
/// committed continuation introduced later.
fn recognize_type_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<TypeStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let type_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first) {
        let Some(trivia) = mod_trivia(type_base, &mut i) else {
            i.rollback(checkpoint);
            return None;
        };
        let Some(keyword) = i.run(scan_word) else {
            i.rollback(checkpoint);
            return None;
        };
        (Some(visibility), Some(trivia), keyword)
    } else {
        (None, None, first)
    };
    if keyword.text() != "type" {
        i.rollback(checkpoint);
        return None;
    }
    Some(TypeStatementIntro {
        start,
        visibility,
        after_visibility,
        type_keyword: keyword,
        type_base,
    })
}

/// Scans the optional, same-line-only declaration parameter production.
///
/// A missing first item rolls back its leading trivia and leaves no list for
/// the enclosing declaration.  Once an item has been accepted, the same
/// transaction is repeated greedily; a non-parameter head belongs to the
/// following definition-introducer slot rather than parameter recovery.
fn scan_declaration_type_parameter_list<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<Vec<DeclarationTypeParameter<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let list_checkpoint = i.checkpoint();
    let mut parameters = Vec::new();

    loop {
        let checkpoint = i.checkpoint();
        if scan_required_inline_trivia(i).is_none() {
            i.rollback(checkpoint);
            break;
        }
        let Some(parameter) = scan_declaration_type_parameter(i) else {
            i.rollback(checkpoint);
            break;
        };
        parameters.push(parameter);
    }

    if parameters.is_empty() {
        i.rollback(list_checkpoint);
        None
    } else {
        Some(parameters)
    }
}

/// Applies Type-declaration's local raw-word policy after the shared path
/// segment scanner has preserved any historical sigil spelling.
fn scan_declaration_type_parameter<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<DeclarationTypeParameter<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let Some(word) = i.run(scan_path_segment) else {
        i.rollback(checkpoint);
        return None;
    };
    match word.text().chars().next() {
        Some('$' | '&' | '\'') => Some(DeclarationTypeParameter::SigilIdentifier(word)),
        _ if type_declaration_parameter_raw_word(word) => {
            Some(DeclarationTypeParameter::Identifier(word))
        }
        _ => {
            i.rollback(checkpoint);
            None
        }
    }
}

/// This is intentionally local rather than a global reserved-word state:
/// declaration parameters accept only words that the historical scanner would
/// have classified as ordinary identifiers at this grammar position.
fn type_declaration_parameter_raw_word(word: WordSpan<'_>) -> bool {
    !matches!(
        word.text(),
        "use"
            | "mod"
            | "struct"
            | "type"
            | "for"
            | "realm"
            | "band"
            | "as"
            | "without"
            | "with"
            | "infix"
            | "my"
            | "pub"
            | "our"
            | "lazy"
            | "prefix"
            | "suffix"
            | "nullfix"
            | "if"
            | "case"
            | "catch"
            | "where"
            | "elsif"
            | "else"
            | "impl"
            | "derives"
    )
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedTypeDeclarationHeader<'source> {
    name: Recovered<WordSpan<'source>>,
    parameters: Vec<DeclarationTypeParameter<'source>>,
    equals: Recovered<Range<usize>>,
    rhs_retry: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum TypeDeclarationHeaderRecovery {
    Missing {
        role: crate::session::TypeDeclarationRole,
        at: usize,
    },
    Error {
        role: crate::session::TypeDeclarationRole,
        range: Range<usize>,
    },
}

/// Parses Type's pre-RHS slots without making the declaration reachable from a
/// real statement consumer.  Gate 5 owns the mandatory RHS itself; this helper
/// reports only whether that later slot may retry at the current cursor.
fn parse_type_declaration_header_slots<'source, E>(
    intro: &TypeStatementIntro<'source>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (ParsedTypeDeclarationHeader<'source>, Vec<TypeDeclarationHeaderRecovery>)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut recoveries = Vec::new();
    let name_boundary = any_ambient_owner_claims(i);
    if !name_boundary {
        let _ = mod_trivia(intro.type_base, i);
    }
    let mut name_incomplete = false;
    let name = if name_boundary {
        name_incomplete = true;
        recoveries.push(TypeDeclarationHeaderRecovery::Missing {
            role: crate::session::TypeDeclarationRole::Name,
            at: i.pos(),
        });
        Recovered::Incomplete
    } else if let Some(name) = i.run(scan_word) {
        Recovered::Complete(name)
    } else {
        match scan_type_declaration_name_invalid_run(i) {
            Some(recovery) => {
                recoveries.push(TypeDeclarationHeaderRecovery::Error {
                    role: crate::session::TypeDeclarationRole::Name,
                    range: recovery.range,
                });
                match recovery.target {
                    TypeDeclarationInvalidTarget::RawName => Recovered::Complete(
                        i.run(scan_word)
                            .expect("a Type name retry must leave its raw word at the cursor"),
                    ),
                    TypeDeclarationInvalidTarget::Equals | TypeDeclarationInvalidTarget::Boundary => {
                        name_incomplete = true;
                        Recovered::Incomplete
                    }
                    TypeDeclarationInvalidTarget::Rhs => {
                        unreachable!("name recovery never retries a RHS")
                    }
                }
            }
            None => {
                name_incomplete = true;
                recoveries.push(TypeDeclarationHeaderRecovery::Missing {
                    role: crate::session::TypeDeclarationRole::Name,
                    at: i.pos(),
                });
                Recovered::Incomplete
            }
        }
    };

    let parameters = if matches!(name, Recovered::Complete(_)) {
        scan_declaration_type_parameter_list(i).unwrap_or_default()
    } else {
        Vec::new()
    };

    let definition_boundary = any_ambient_owner_claims(i);
    if !definition_boundary {
        let continuation_checkpoint = i.checkpoint();
        if mod_trivia(intro.type_base, i).is_none() {
            i.rollback(continuation_checkpoint);
        }
    }

    let (equals, rhs_retry) = if let Some(equals) = i.run(scan_declaration_exact_equals) {
        (Recovered::Complete(equals), true)
    } else if name_incomplete {
        (Recovered::Incomplete, false)
    } else if definition_boundary {
        recoveries.push(TypeDeclarationHeaderRecovery::Missing {
            role: crate::session::TypeDeclarationRole::DefinitionIntroducer,
            at: i.pos(),
        });
        (Recovered::Incomplete, false)
    } else {
        match scan_type_declaration_definition_invalid_run(intro.type_base, i) {
            Some(recovery) => {
                recoveries.push(TypeDeclarationHeaderRecovery::Error {
                    role: crate::session::TypeDeclarationRole::DefinitionIntroducer,
                    range: recovery.range,
                });
                match recovery.target {
                    TypeDeclarationInvalidTarget::Equals => {
                        let equals = i
                            .run(scan_declaration_exact_equals)
                            .expect("definition-introducer retry must leave exact equals at the cursor");
                        (Recovered::Complete(equals), true)
                    }
                    TypeDeclarationInvalidTarget::Rhs => (Recovered::Incomplete, true),
                    TypeDeclarationInvalidTarget::Boundary => (Recovered::Incomplete, false),
                    TypeDeclarationInvalidTarget::RawName => {
                        unreachable!("definition-introducer recovery never retries a declaration name")
                    }
                }
            }
            None if type_declaration_rhs_candidate_pending(i) => {
                recoveries.push(TypeDeclarationHeaderRecovery::Missing {
                    role: crate::session::TypeDeclarationRole::DefinitionIntroducer,
                    at: i.pos(),
                });
                (Recovered::Incomplete, true)
            }
            None => {
                recoveries.push(TypeDeclarationHeaderRecovery::Missing {
                    role: crate::session::TypeDeclarationRole::DefinitionIntroducer,
                    at: i.pos(),
                });
                (Recovered::Incomplete, false)
            }
        }
    };

    (
        ParsedTypeDeclarationHeader { name, parameters, equals, rhs_retry },
        recoveries,
    )
}

/// Direct-CST's isolated header harness shares the AST scanner and merely
/// realizes its selected recoveries as committed typed records.
fn commit_type_declaration_header_slots<'parse, 'source, 'local, E, O>(
    intro: &TypeStatementIntro<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> ParsedTypeDeclarationHeader<'source>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let (header, recoveries) = committed.probe(|probe| {
        parse_type_declaration_header_slots(intro, probe.input())
    });
    for recovery in recoveries {
        emit_type_declaration_header_recovery(committed, recovery);
    }
    header
}

fn type_declaration_rhs_role() -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Type(
        crate::session::TypeDeclarationRole::Rhs,
    ))
}

/// Owns the complete Type-declaration RHS episode. No caller can enter the
/// mandatory TypeExpression without first passing the original-gap ambient
/// check and installing the declaration baseline and stop scope here.
fn parse_type_declaration_rhs<'source, E>(
    header: &ParsedTypeDeclarationHeader<'source>,
    type_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if !header.rhs_retry || any_ambient_owner_claims(i) {
        return Recovered::Incomplete;
    }
    let trivia_checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(type_base, i) else {
        i.rollback(trivia_checkpoint);
        return Recovered::Incomplete;
    };

    let baseline = IndentationBaseline {
        column: type_base,
        kind: IndentationBaselineKind::Introducer,
    };
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
        .with(StopKind::Semicolon)
        .with(StopKind::With);
    i.local.push_indentation_baseline(baseline);
    i.local.push_stop_set(stops);
    let rhs = i
        .run(from_fn(|i| {
            Some(parse_required_type_expression_with_outer_missing_role(
                Some(type_declaration_rhs_role()),
                i,
            ))
        }))
        .expect("the mandatory Type declaration RHS entry is total");
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_indentation_baseline(), Some(baseline));

    match rhs {
        Recovered::Complete(rhs) => Recovered::Complete(Box::new(rhs)),
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

/// Direct-CST counterpart of [`parse_type_declaration_rhs`]. The same helper
/// owns trivia emission, state setup, mandatory parsing, and exact teardown.
fn commit_type_declaration_rhs<'parse, 'source, 'local, E, O>(
    header: &ParsedTypeDeclarationHeader<'source>,
    type_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if !header.rhs_retry {
        return Recovered::Incomplete;
    }
    if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        let at = committed.probe(|probe| probe.input().pos());
        emit_type_declaration_header_recovery(
            committed,
            TypeDeclarationHeaderRecovery::Missing {
                role: crate::session::TypeDeclarationRole::Rhs,
                at,
            },
        );
        return Recovered::Incomplete;
    }
    let trivia = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let trivia = mod_trivia(type_base, i);
        if trivia.is_none() {
            i.rollback(checkpoint);
        }
        trivia
    });
    let Some(trivia) = trivia else {
        let at = committed.probe(|probe| probe.input().pos());
        emit_type_declaration_header_recovery(
            committed,
            TypeDeclarationHeaderRecovery::Missing {
                role: crate::session::TypeDeclarationRole::Rhs,
                at,
            },
        );
        return Recovered::Incomplete;
    };
    committed.emit_trivia(&trivia);

    let baseline = IndentationBaseline {
        column: type_base,
        kind: IndentationBaselineKind::Introducer,
    };
    let stops = committed.probe(|probe| {
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
            .with(StopKind::Semicolon)
            .with(StopKind::With)
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_indentation_baseline(baseline);
        i.local.push_stop_set(stops);
    });
    let rhs = commit_direct_type_expression_with_outer_missing_role(
        Some(type_declaration_rhs_role()),
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        assert_eq!(i.local.pop_indentation_baseline(), Some(baseline));
    });
    let range = rhs.range();
    if range.is_empty() {
        Recovered::Incomplete
    } else {
        Recovered::Complete(range)
    }
}

pub(crate) fn parse_type_declaration<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<TypeDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let intro = i.run(recognize_type_statement_intro)?;
    let (header, _) = parse_type_declaration_header_slots(&intro, &mut i);
    let rhs = parse_type_declaration_rhs(&header, intro.type_base, &mut i);
    let range = intro.start..i.pos();
    Some(TypeDeclaration {
        visibility: intro
            .visibility
            .map_or(Visibility::Private, |prefix| prefix.visibility),
        name: header.name,
        parameters: header.parameters,
        equals: header.equals,
        rhs,
        range,
    })
}

/// Emits the production CST continuation selected by the shared Type intro.
/// Header recognition remains sink-free, then this adapter replays only the
/// accepted source spans in source order before entering the atomic RHS owner.
pub(crate) fn commit_type_declaration<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: TypeStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::TypeDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::TypeKw, intro.type_keyword.range());

    let (header, recoveries, header_end) = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let (header, recoveries) = parse_type_declaration_header_slots(&intro, i);
        let end = i.pos();
        i.rollback(checkpoint);
        (header, recoveries, end)
    });
    commit_type_declaration_header_surface(
        intro.type_base,
        &header,
        recoveries,
        header_end,
        committed,
    );
    let _ = commit_type_declaration_rhs(&header, intro.type_base, committed);
    let end = committed.probe(|probe| probe.input().pos());
    committed.finish_node();
    Recovered::Complete(intro.start..end)
}

fn commit_type_declaration_header_surface<'parse, 'source, 'local, E, O>(
    type_base: usize,
    header: &ParsedTypeDeclarationHeader<'source>,
    recoveries: Vec<TypeDeclarationHeaderRecovery>,
    header_end: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let name_recovery = recoveries.iter().find(|recovery| {
        type_declaration_header_recovery_role(recovery)
            == crate::session::TypeDeclarationRole::Name
    });
    let definition_recovery = recoveries.iter().find(|recovery| {
        type_declaration_header_recovery_role(recovery)
            == crate::session::TypeDeclarationRole::DefinitionIntroducer
    });

    let name_target = name_recovery
        .map(type_declaration_header_recovery_start)
        .or_else(|| match &header.name {
            Recovered::Complete(name) => Some(name.range().start),
            Recovered::Incomplete => None,
        })
        .or_else(|| definition_recovery.map(type_declaration_header_recovery_start))
        .or_else(|| match &header.equals {
            Recovered::Complete(equals) => Some(equals.start),
            Recovered::Incomplete => None,
        })
        .unwrap_or(header_end);
    commit_type_declaration_continuation_trivia_until(type_base, name_target, committed);
    if let Some(recovery) = name_recovery {
        commit_type_declaration_header_recovery(recovery.clone(), committed);
    }
    if let Recovered::Complete(expected) = &header.name {
        let actual = commit_word(committed).expect("accepted Type name remains at the cursor");
        debug_assert_eq!(actual.range(), expected.range());
        committed.token(SyntaxKind::Identifier, actual.range());
    }

    if !header.parameters.is_empty() {
        committed.start_node(SyntaxKind::DeclarationTypeParameterList);
        for parameter in &header.parameters {
            let trivia = committed
                .probe(|probe| scan_required_inline_trivia(probe.input()))
                .expect("an accepted Type parameter retains its same-line separator");
            committed.emit_trivia(&trivia);
            let actual = committed
                .probe(|probe| probe.input().run(scan_path_segment))
                .expect("an accepted Type parameter remains at the cursor");
            debug_assert_eq!(actual.range(), declaration_type_parameter_range(parameter));
            committed.token(declaration_type_parameter_kind(parameter), actual.range());
        }
        committed.finish_node();
    }

    let definition_target = definition_recovery
        .map(type_declaration_header_recovery_start)
        .or_else(|| match &header.equals {
            Recovered::Complete(equals) => Some(equals.start),
            Recovered::Incomplete => None,
        })
        .unwrap_or(header_end);
    commit_type_declaration_continuation_trivia_until(
        type_base,
        definition_target,
        committed,
    );
    if let Some(recovery) = definition_recovery {
        commit_type_declaration_header_recovery(recovery.clone(), committed);
    }
    if let Recovered::Complete(expected) = &header.equals {
        let actual = committed
            .probe(|probe| probe.input().run(scan_declaration_exact_equals))
            .expect("accepted Type definition introducer remains at the cursor");
        debug_assert_eq!(&actual, expected);
        committed.token(SyntaxKind::Equals, actual);
    }
    debug_assert_eq!(committed.probe(|probe| probe.input().pos()), header_end);
}

fn commit_type_declaration_continuation_trivia_until<'parse, 'source, 'local, E, O>(
    type_base: usize,
    target: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let current = committed.probe(|probe| probe.input().pos());
    if current == target {
        return;
    }
    let trivia = committed
        .probe(|probe| mod_trivia(type_base, probe.input()))
        .expect("accepted Type header trivia remains at the cursor");
    debug_assert_eq!(trivia.range(), current..target);
    committed.emit_trivia(&trivia);
}

fn commit_type_declaration_header_recovery<'parse, 'source, 'local, E, O>(
    recovery: TypeDeclarationHeaderRecovery,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let TypeDeclarationHeaderRecovery::Error { range, .. } = &recovery {
        committed.probe(|probe| {
            let i = probe.input();
            debug_assert_eq!(i.pos(), range.start);
            while i.pos() < range.end {
                i.input
                    .next()
                    .expect("a selected Type header error range remains available");
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            debug_assert_eq!(i.pos(), range.end);
        });
    }
    emit_type_declaration_header_recovery(committed, recovery);
}

fn type_declaration_header_recovery_role(
    recovery: &TypeDeclarationHeaderRecovery,
) -> crate::session::TypeDeclarationRole {
    match recovery {
        TypeDeclarationHeaderRecovery::Missing { role, .. }
        | TypeDeclarationHeaderRecovery::Error { role, .. } => *role,
    }
}

fn type_declaration_header_recovery_start(recovery: &TypeDeclarationHeaderRecovery) -> usize {
    match recovery {
        TypeDeclarationHeaderRecovery::Missing { at, .. } => *at,
        TypeDeclarationHeaderRecovery::Error { range, .. } => range.start,
    }
}

fn declaration_type_parameter_range(parameter: &DeclarationTypeParameter<'_>) -> Range<usize> {
    match parameter {
        DeclarationTypeParameter::Identifier(word)
        | DeclarationTypeParameter::SigilIdentifier(word) => word.range(),
    }
}

fn declaration_type_parameter_kind(parameter: &DeclarationTypeParameter<'_>) -> SyntaxKind {
    match parameter {
        DeclarationTypeParameter::Identifier(_) => SyntaxKind::Identifier,
        DeclarationTypeParameter::SigilIdentifier(_) => SyntaxKind::SigilIdentifier,
    }
}

fn emit_type_declaration_header_recovery<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    recovery: TypeDeclarationHeaderRecovery,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let (kind, role, range, unexpected) = match recovery {
        TypeDeclarationHeaderRecovery::Missing { role, at } => {
            (RecoveryKind::Missing, role, at..at, Arc::from([]))
        }
        TypeDeclarationHeaderRecovery::Error { role, range } => {
            let unexpected = Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]);
            (RecoveryKind::Error, role, range, unexpected)
        }
    };
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Type(role));
        let expected = match role {
            GrammarRole::Declaration(DeclarationRole::Type(
                crate::session::TypeDeclarationRole::Name,
            )) => ExpectedSyntax::Identifier,
            GrammarRole::Declaration(DeclarationRole::Type(
                crate::session::TypeDeclarationRole::DefinitionIntroducer,
            )) => ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Equals),
            GrammarRole::Declaration(DeclarationRole::Type(
                crate::session::TypeDeclarationRole::Rhs,
            )) => ExpectedSyntax::TypeExpression,
            _ => unreachable!("Type header recovery has only Type declaration roles"),
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role, range: range.clone() },
            kind,
            unexpected,
            Arc::from([SyntaxExpectation {
                role,
                expected,
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    match kind {
        RecoveryKind::Missing => committed.emit_missing(record),
        RecoveryKind::Error => committed.emit_error(record),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeDeclarationInvalidTarget {
    RawName,
    Equals,
    Rhs,
    Boundary,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TypeDeclarationInvalidRun {
    range: Range<usize>,
    target: TypeDeclarationInvalidTarget,
}

fn scan_type_declaration_name_invalid_run<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<TypeDeclarationInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_type_declaration_invalid_run(i, |i| {
        type_declaration_raw_name_pending(i).then_some(TypeDeclarationInvalidTarget::RawName)
    })
}

fn scan_type_declaration_definition_invalid_run<'source, E>(
    type_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<TypeDeclarationInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_type_declaration_invalid_run(i, |i| {
        if type_declaration_terminal_boundary_pending(type_base, i) {
            Some(TypeDeclarationInvalidTarget::Boundary)
        } else if type_declaration_rhs_candidate_pending(i) {
            Some(TypeDeclarationInvalidTarget::Rhs)
        } else {
            None
        }
    })
}

fn scan_type_declaration_invalid_run<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
    retry_candidate: impl Fn(&mut SynIn<'_, 'source, '_, E>) -> Option<TypeDeclarationInvalidTarget>,
) -> Option<TypeDeclarationInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if declaration_exact_equals_pending(i) {
            return (start < i.pos()).then_some(TypeDeclarationInvalidRun {
                range: start..i.pos(),
                target: TypeDeclarationInvalidTarget::Equals,
            });
        }
        if let Some(target) = retry_candidate(i) {
            return (start < i.pos()).then_some(TypeDeclarationInvalidRun {
                range: start..i.pos(),
                target,
            });
        }
        if type_declaration_terminal_boundary_pending(usize::MAX, i) {
            return (start < i.pos()).then_some(TypeDeclarationInvalidRun {
                range: start..i.pos(),
                target: TypeDeclarationInvalidTarget::Boundary,
            });
        }
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(TypeDeclarationInvalidRun {
                range: start..i.pos(),
                target: TypeDeclarationInvalidTarget::Boundary,
            });
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn type_declaration_raw_name_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_word).is_some();
    i.rollback(checkpoint);
    pending
}

fn declaration_exact_equals_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_declaration_exact_equals).is_some();
    i.rollback(checkpoint);
    pending
}

fn type_declaration_rhs_candidate_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(parse_type_expression).is_some();
    i.rollback(checkpoint);
    pending
}

fn type_declaration_terminal_boundary_pending<E>(type_base: usize, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty()
        || matches!(i.input.remainder().chars().next(), Some(';'))
        || any_ambient_owner_claims(i)
    {
        return true;
    }
    if type_base == usize::MAX {
        return false;
    }
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia);
    let pending = trivia.is_some_and(|trivia| {
        i.input.source()[trivia.range()].contains(['\r', '\n'])
            && i.local.line().line_indent <= type_base
    });
    i.rollback(checkpoint);
    pending
}

fn recognize_mod_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ModStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let base = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first) {
        let Some(trivia) = mod_trivia(base, &mut i) else {
            i.rollback(checkpoint);
            return None;
        };
        let Some(keyword) = i.run(scan_word) else {
            i.rollback(checkpoint);
            return None;
        };
        (Some(visibility), Some(trivia), keyword)
    } else {
        (None, None, first)
    };
    if keyword.text() != "mod" {
        i.rollback(checkpoint);
        return None;
    }
    Some(ModStatementIntro { start, visibility, after_visibility, mod_keyword: keyword })
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
        let Some(visibility_keyword) = i.run(scan_word) else {
            return false;
        };
        if visibility_prefix(visibility_keyword).is_none() {
            return false;
        }
        let Some(_) = scan_required_inline_trivia(i) else {
            return true;
        };
        let Some(target_head) = i.run(scan_word) else {
            return true;
        };
        if target_head.text() == "use" {
            let use_checkpoint = i.checkpoint();
            let selected_as_use = scan_required_inline_trivia(i).is_some()
                && parse_use_tree(i).is_some();
            i.rollback(use_checkpoint);
            return !selected_as_use;
        }
        if target_head.text() == "mod" {
            return false;
        }
        if matches!(target_head.text(), "lazy" | "prefix" | "infix" | "suffix" | "nullfix") {
            let definition_checkpoint = i.checkpoint();
            let binding_base = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
            let is_binding_definition = binding_trivia(binding_base, i).is_some()
                && i.run(scan_declaration_exact_equals).is_some();
            i.rollback(definition_checkpoint);
            return is_binding_definition;
        }
        true
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

/// Unlike the mandatory scanner used after a continuation has committed, an
/// intro may inspect this slot without consuming a newline or EOF boundary.
fn scan_maybe_required_inline_trivia<E>(i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = scan_required_inline_trivia(i);
    if trivia.is_none() {
        i.rollback(checkpoint);
    }
    trivia
}

fn scan_maybe_optional_inline_trivia<E>(i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = scan_optional_inline_trivia(i);
    if trivia.is_none() {
        i.rollback(checkpoint);
    }
    trivia
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

/// Recognizes one visibility prefix of a binding statement without giving the
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
    let keyword = i.run(scan_word)?;
    let visibility = visibility_prefix(keyword)?;
    Some(BindingStatementIntro { start, visibility })
}

/// Commits one binding declaration without reconstructing its AST from CST.
pub(crate) fn commit_binding_declaration<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: BindingStatementIntro<'source>,
) -> Recovered<ParsedBindingDeclaration<'source, O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::BindingStatement);
    committed.start_node(SyntaxKind::BindingHeader);
    emit_visibility(committed, &intro.visibility);
    let binding_base = committed.probe(|probe| {
        probe.input().local.indentation_baseline().map_or(0, |baseline| baseline.column)
    });
    let target_trivia = committed.probe(|probe| binding_trivia(binding_base, probe.input()));
    if let Some(trivia) = &target_trivia {
        committed.emit_trivia(trivia);
    }
    let stops = committed.probe(|probe| probe.input().local.stop_set().unwrap_or_default().with(StopKind::Equal));
    committed.probe(|probe| probe.input().local.push_stop_set(stops));
    let target = parse_direct_pattern_with_outer_missing_role(
        operators,
        LeadingTrivia::None,
        Some(GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Target))),
        committed,
    )
        .map_or_else(
            || {
                emit_binding_missing(committed, BindingRole::Target, ExpectedSyntax::Pattern);
                Recovered::Incomplete
            },
            Recovered::Complete,
        );
    committed.probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stops)));
    let definition_intro = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let Some(trivia) = binding_trivia(binding_base, i) else {
            i.rollback(checkpoint);
            return None;
        };
        let Some(equals) = i.run(scan_declaration_exact_equals) else {
            i.rollback(checkpoint);
            return None;
        };
        Some((trivia, equals))
    });
    if let Some((trivia, equals)) = &definition_intro {
        committed.emit_trivia(trivia);
        committed.token(SyntaxKind::Equals, equals.clone());
    }
    committed.finish_node();

    let definition = definition_intro.map(|(_trivia, equals)| {
        committed.start_node(SyntaxKind::BindingBody);
        let body = commit_binding_body(operators, binding_base, committed);
        let end = match &body {
            Recovered::Complete(body) => body.range().end,
            Recovered::Incomplete => equals.end,
        };
        committed.finish_node();
        ParsedBindingDefinition { equals: equals.clone(), body, range: equals.start..end }
    });
    let end = definition.as_ref().map_or_else(
        || match &target {
            Recovered::Complete(target) => target.range().end,
            Recovered::Incomplete => committed.probe(|probe| probe.input().pos()),
        },
        |definition| definition.range.end,
    );
    committed.finish_node();
    Recovered::Complete(ParsedBindingDeclaration {
        visibility: intro.visibility.visibility,
        range: intro.start..end,
        target,
        definition,
        marker: std::marker::PhantomData,
    })
}

/// Commits the total Mod continuation selected by the shared statement intro.
/// Identity and body slots stay local to this node so root and nested callers
/// cannot accidentally assign their boundary recovery to different owners.
pub(crate) fn commit_mod_declaration<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: ModStatementIntro<'source>,
) -> Recovered<()>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::ModDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
        let base = committed.probe(|probe| probe.input().local.indentation_baseline().map_or(0, |baseline| baseline.column));
        let _ = base;
    }
    committed.token(SyntaxKind::ModKw, intro.mod_keyword.range());
    let mod_base = committed.probe(|probe| probe.input().local.indentation_baseline().map_or(0, |baseline| baseline.column));
    if let Some(trivia) = committed.probe(|probe| mod_trivia(mod_base, probe.input())) {
        committed.emit_trivia(&trivia);
    }

    let mut identity_missing = false;
    let mut identity_error = false;
    let first = commit_word(committed).or_else(|| match mod_word_error_retry(committed, ModRole::Name) {
        Some(true) => commit_word(committed),
        Some(false) => { identity_error = true; None }
        None => None,
    });
    let is_test = first.as_ref().is_some_and(|word| word.text() == "test");
    if is_test {
        let marker = first.expect("checked above");
        committed.start_node(SyntaxKind::TestModuleMarker);
        committed.token(SyntaxKind::Identifier, marker.range());
        committed.finish_node();
        let anonymous = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let result = mod_trivia(mod_base, i).is_some() && mod_body_starter_pending(i);
            i.rollback(checkpoint);
            result
        });
        if !anonymous {
            if let Some(trivia) = committed.probe(|probe| mod_trivia(mod_base, probe.input())) {
                committed.emit_trivia(&trivia);
            }
            let name = commit_word(committed).or_else(|| match mod_word_error_retry(committed, ModRole::TestName) {
                Some(true) => commit_word(committed),
                Some(false) => {
                    identity_error = true;
                    None
                }
                None => None,
            });
            if let Some(name) = name {
                committed.token(SyntaxKind::Identifier, name.range());
            } else if !identity_error {
                emit_mod_missing(committed, ModRole::TestName, ExpectedSyntax::Identifier);
                identity_missing = true;
            } else {
                identity_missing = true;
            }
        }
    } else if let Some(name) = first {
        committed.token(SyntaxKind::Identifier, name.range());
    } else if !identity_error {
        emit_mod_missing(committed, ModRole::Name, ExpectedSyntax::Identifier);
        identity_missing = true;
    } else {
        identity_missing = true;
    }

    if let Some(trivia) = committed.probe(|probe| mod_trivia(mod_base, probe.input())) {
        committed.emit_trivia(&trivia);
    }
    let mut body_starter = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let starter = i.run(scan_punctuation).and_then(|punctuation| match punctuation.kind() {
            PunctuationKind::Semicolon => Some(PunctuationKind::Semicolon),
            PunctuationKind::Open(Delimiter::Brace) => Some(PunctuationKind::Open(Delimiter::Brace)),
            PunctuationKind::Colon => Some(PunctuationKind::Colon),
            _ => None,
        });
        i.rollback(checkpoint);
        starter
    });
    let mut body_introducer_error = false;
    if body_starter.is_none() && !identity_missing {
        let statement_pending = committed.probe(|probe| {
            crate::grammar::expression::direct_canonical_statement_candidate(
                operators,
                LeadingTrivia::None,
                probe,
            )
        });
        if !statement_pending && mod_body_introducer_error_retry(operators, committed).is_some() {
            body_introducer_error = true;
            body_starter = committed.probe(|probe| {
                let i = probe.input();
                let checkpoint = i.checkpoint();
                let starter = i.run(scan_punctuation).and_then(|punctuation| match punctuation.kind() {
                    PunctuationKind::Semicolon => Some(PunctuationKind::Semicolon),
                    PunctuationKind::Open(Delimiter::Brace) => Some(PunctuationKind::Open(Delimiter::Brace)),
                    PunctuationKind::Colon => Some(PunctuationKind::Colon),
                    _ => None,
                });
                i.rollback(checkpoint);
                starter
            });
        }
    }
    match body_starter {
        Some(PunctuationKind::Semicolon) => {
            let punctuation = committed.probe(|probe| probe.input().run(scan_punctuation)).expect("accepted starter remains");
            committed.token(SyntaxKind::Semicolon, punctuation.range());
        }
        Some(PunctuationKind::Open(Delimiter::Brace)) => {
            let punctuation = committed.probe(|probe| probe.input().run(scan_punctuation)).expect("accepted starter remains");
            commit_braced_statement_block_expression(operators, punctuation.range(), committed);
        }
        Some(PunctuationKind::Colon) => {
            let punctuation = committed.probe(|probe| probe.input().run(scan_punctuation)).expect("accepted starter remains");
            committed.token(SyntaxKind::Colon, punctuation.range());
            commit_mod_colon_body(operators, mod_base, committed);
        }
        Some(_) | None => {
            if identity_missing {
                committed.finish_node();
                return Recovered::Complete(());
            }
            let candidate = committed.probe(|probe| {
                crate::grammar::expression::direct_canonical_statement_candidate(
                    operators,
                    LeadingTrivia::None,
                    probe,
                )
            });
            if candidate {
                if !body_introducer_error {
                    emit_mod_missing(
                        committed,
                        ModRole::BodyIntroducer,
                        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
                    );
                }
                let _ = commit_mod_inline_statement(operators, committed);
            } else if !body_introducer_error {
                emit_mod_body_introducer_missing(committed);
            }
        }
    }
    committed.finish_node();
    Recovered::Complete(())
}

/// Commits the selected Struct prefix while the declaration body parser is
/// introduced in later slices. The selected keyword is never returned to the
/// binding or expression alternatives.
pub(crate) fn commit_struct_declaration<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: StructStatementIntro<'source>,
) -> Recovered<()>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::StructDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::StructKw, intro.struct_keyword.range());

    if let Some(trivia) = committed.probe(|probe| {
        struct_continuation_trivia(intro.struct_base, probe.input())
    }) {
        committed.emit_trivia(&trivia);
    }

    let mut name_incomplete = false;
    if let Some(name) = commit_word(committed) {
        committed.token(SyntaxKind::Identifier, name.range());
    } else {
        match struct_name_error_retry(committed) {
            Some(true) => {
                let name = commit_word(committed)
                    .expect("a Struct name retry must leave its raw word at the cursor");
                committed.token(SyntaxKind::Identifier, name.range());
            }
            Some(false) => {
                name_incomplete = true;
            }
            None => {
                name_incomplete = true;
                emit_struct_missing(committed, crate::session::StructRole::Name, ExpectedSyntax::Identifier);
            }
        }
    }

    let body_starter_pending = committed.probe(|probe| struct_body_starter_pending(probe.input()));
    if !name_incomplete || body_starter_pending {
        if let Some(trivia) = committed.probe(|probe| {
            struct_continuation_trivia(intro.struct_base, probe.input())
        }) {
            committed.emit_trivia(&trivia);
        }
        commit_struct_body_introducer(intro.struct_base, committed);
    }
    committed.finish_node();
    Recovered::Complete(())
}

fn commit_struct_body_introducer<'parse, 'source, 'local, E, O>(
    struct_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut starter = committed.probe(|probe| struct_body_starter(probe.input()));
    let mut body_introducer_error = false;
    if starter.is_none() && !commit_word_candidate(committed) {
        match struct_body_introducer_error_retry(committed) {
            Some(true) => {
                starter = committed.probe(|probe| struct_body_starter(probe.input()));
            }
            Some(false) => body_introducer_error = true,
            None => {}
        }
    }

    match starter {
        Some(StructBodyStarter::Bodyless(range)) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("a selected Struct semicolon remains available");
            debug_assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Semicolon, range);
        }
        Some(StructBodyStarter::NamedBraced(range)) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("a selected Struct brace remains available");
            debug_assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::LBrace, range.clone());
            commit_struct_named_braced_body(struct_base, range, committed);
        }
        Some(StructBodyStarter::Tuple(range)) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("a selected Struct parenthesis remains available");
            debug_assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::LParen, range.clone());
            commit_struct_tuple_body(struct_base, range, committed);
        }
        Some(StructBodyStarter::NamedIndented(range)) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("a selected Struct colon remains available");
            debug_assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Colon, range.clone());
            commit_struct_named_indented_body(struct_base, range, committed);
        }
        None if !body_introducer_error => emit_struct_body_introducer_missing(committed),
        None => {}
    }
}

fn commit_struct_named_indented_body<'parse, 'source, 'local, E, O>(
    struct_base: usize,
    colon: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let opening = committed.probe(|probe| consume_struct_indented_opening(struct_base, probe.input()));
    let Some((opening, block_indent)) = opening else {
        emit_struct_missing(committed, crate::session::StructRole::Field, ExpectedSyntax::Identifier);
        return;
    };
    committed.emit_trivia(&opening);
    let stops = committed.probe(|probe| {
        probe.input().local.stop_set().unwrap_or_default()
            .without(StopKind::Newline)
            .with(StopKind::Comma)
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(stops);
        push_struct_indented_layout(block_indent, i);
    });

    let mut field_count = 0usize;
    loop {
        if committed.probe(|probe| struct_indented_terminal_boundary_pending(block_indent, probe.input())) {
            if field_count == 0 {
                commit_empty_struct_named_field(committed);
            }
            break;
        }
        if committed.probe(|probe| scan_struct_comma_pending(probe.input())) {
            commit_empty_struct_named_field(committed);
            field_count += 1;
            let comma = committed
                .probe(|probe| scan_struct_comma(probe.input()))
                .expect("the empty Struct field slot is followed by its comma");
            committed.token(SyntaxKind::Comma, comma);
            match commit_struct_indented_gap(block_indent, committed) {
                StructIndentedGap::Dedent => break,
                StructIndentedGap::Trivia(_) if committed.probe(|probe| {
                    struct_indented_terminal_boundary_pending(block_indent, probe.input())
                }) => break,
                StructIndentedGap::Trivia(_) => continue,
            }
        }
        if let Some(semicolon) = committed.probe(|probe| scan_struct_semicolon(probe.input())) {
            emit_struct_error(
                committed,
                crate::session::StructRole::FieldSeparator,
                semicolon,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            match commit_struct_indented_gap(block_indent, committed) {
                StructIndentedGap::Dedent => break,
                StructIndentedGap::Trivia(_) => continue,
            }
        }

        if !commit_struct_named_field(false, committed) {
            if let Some(run) = committed.probe(|probe| scan_struct_field_invalid_run(false, probe.input())) {
                emit_struct_error(
                    committed,
                    crate::session::StructRole::Field,
                    run.range,
                    ExpectedSyntax::Identifier,
                );
                field_count += 1;
                match commit_struct_indented_gap(block_indent, committed) {
                    StructIndentedGap::Dedent => break,
                    StructIndentedGap::Trivia(_) => continue,
                }
            } else {
                commit_empty_struct_named_field(committed);
                break;
            }
        }
        field_count += 1;

        let gap = commit_struct_indented_gap(block_indent, committed);
        if matches!(gap, StructIndentedGap::Dedent) {
            break;
        }
        let StructIndentedGap::Trivia(trivia) = gap else { unreachable!() };
        let newline_boundary = committed.probe(|probe| {
            struct_trivia_has_newline(&trivia)
                && probe.input().local.line().line_indent == block_indent
        });
        if newline_boundary {
            continue;
        }
        if let Some(comma) = committed.probe(|probe| scan_struct_comma(probe.input())) {
            committed.token(SyntaxKind::Comma, comma);
            match commit_struct_indented_gap(block_indent, committed) {
                StructIndentedGap::Dedent => break,
                StructIndentedGap::Trivia(_) if committed.probe(|probe| {
                    struct_indented_terminal_boundary_pending(block_indent, probe.input())
                }) => break,
                StructIndentedGap::Trivia(_) => continue,
            }
        }
        if let Some(semicolon) = committed.probe(|probe| scan_struct_semicolon(probe.input())) {
            emit_struct_error(
                committed,
                crate::session::StructRole::FieldSeparator,
                semicolon,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            let _ = commit_struct_indented_gap(block_indent, committed);
            continue;
        }
        if committed.probe(|probe| struct_indented_terminal_boundary_pending(block_indent, probe.input())) {
            break;
        }
        if committed.probe(|probe| struct_next_named_field_candidate(probe.input(), &trivia)) {
            emit_struct_missing(
                committed,
                crate::session::StructRole::FieldSeparator,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            continue;
        }
        break;
    }

    committed.probe(|probe| {
        let i = probe.input();
        pop_struct_indented_layout(block_indent, i);
        assert_eq!(i.local.pop_stop_set(), Some(stops));
    });
    let _ = colon;
}

fn commit_struct_tuple_body<'parse, 'source, 'local, E, O>(
    struct_base: usize,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let stops = committed.probe(|probe| {
        probe.input().local.stop_set().unwrap_or_default()
            .without(StopKind::Newline)
            .with(StopKind::Comma)
            .with(StopKind::RightParenthesis)
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_delimiter(Delimiter::Parenthesis);
        i.local.push_stop_set(stops);
    });
    let opening = committed.probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia is total");
    committed.emit_trivia(&opening);
    let layout = committed.probe(|probe| {
        LayoutDelimitedFrame::after_opening_trivia(
            struct_base,
            &opening,
            probe.input().local.line().line_indent,
        )
    });
    committed.probe(|probe| push_struct_layout(layout, probe.input()));

    loop {
        if let Some(close) = committed.probe(|probe| scan_struct_close_parenthesis(probe.input())) {
            committed.token(SyntaxKind::RParen, close);
            break;
        }
        if committed.probe(|probe| {
            struct_outer_owned_mismatched_close_pending_for(Delimiter::Parenthesis, probe.input())
        }) {
            emit_struct_missing_close_for(
                committed,
                ConstructRole::StructTupleFields,
                Delimiter::Parenthesis,
            );
            break;
        }
        if let Some((range, actual)) = committed.probe(|probe| {
            scan_struct_mismatched_close_for(Delimiter::Parenthesis, probe.input())
        }) {
            emit_struct_mismatched_close_for(
                committed,
                ConstructRole::StructTupleFields,
                Delimiter::Parenthesis,
                range,
                actual,
            );
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close_for(
                    committed,
                    ConstructRole::StructTupleFields,
                    Delimiter::Parenthesis,
                );
                break;
            }
            let trivia = committed.probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if committed.probe(|probe| probe.input().input.remainder().is_empty()) {
            emit_struct_missing_close_for(
                committed,
                ConstructRole::StructTupleFields,
                Delimiter::Parenthesis,
            );
            break;
        }
        if committed.probe(|probe| scan_struct_comma_pending(probe.input())) {
            commit_empty_struct_tuple_field(committed);
            let comma = committed
                .probe(|probe| scan_struct_comma(probe.input()))
                .expect("the empty Struct tuple slot is followed by its comma");
            committed.token(SyntaxKind::Comma, comma);
            let trivia = committed.probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if let Some(semicolon) = committed.probe(|probe| scan_struct_semicolon(probe.input())) {
            emit_struct_error(
                committed,
                crate::session::StructRole::FieldSeparator,
                semicolon,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close_for(
                    committed,
                    ConstructRole::StructTupleFields,
                    Delimiter::Parenthesis,
                );
                break;
            }
            let trivia = committed.probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }

        commit_struct_tuple_field(committed);
        if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
            emit_struct_missing_close_for(
                committed,
                ConstructRole::StructTupleFields,
                Delimiter::Parenthesis,
            );
            break;
        }
        let trivia = committed.probe(|probe| probe.input().run(scan_trivia))
            .expect("trivia is total");
        committed.emit_trivia(&trivia);
        if let Some(comma) = committed.probe(|probe| scan_struct_comma(probe.input())) {
            committed.token(SyntaxKind::Comma, comma);
            let post = committed.probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&post);
            if let Some(close) = committed.probe(|probe| scan_struct_close_parenthesis(probe.input())) {
                committed.token(SyntaxKind::RParen, close);
                break;
            }
            if committed.probe(|probe| {
                probe.input().input.remainder().is_empty()
                    || struct_outer_owned_mismatched_close_pending_for(
                        Delimiter::Parenthesis,
                        probe.input(),
                    )
            }) {
                commit_empty_struct_tuple_field(committed);
                emit_struct_missing_close_for(
                    committed,
                    ConstructRole::StructTupleFields,
                    Delimiter::Parenthesis,
                );
                break;
            }
            continue;
        }
        if let Some(close) = committed.probe(|probe| scan_struct_close_parenthesis(probe.input())) {
            committed.token(SyntaxKind::RParen, close);
            break;
        }
        if committed.probe(|probe| {
            layout.boundary_after_trivia(&trivia, probe.input().local.line().line_indent)
                == LayoutDelimitedBoundary::ImplicitNewline
        }) {
            continue;
        }
        if committed.probe(|probe| {
            struct_outer_owned_mismatched_close_pending_for(Delimiter::Parenthesis, probe.input())
        }) {
            emit_struct_missing_close_for(
                committed,
                ConstructRole::StructTupleFields,
                Delimiter::Parenthesis,
            );
            break;
        }
        if let Some((range, actual)) = committed.probe(|probe| {
            scan_struct_mismatched_close_for(Delimiter::Parenthesis, probe.input())
        }) {
            emit_struct_mismatched_close_for(
                committed,
                ConstructRole::StructTupleFields,
                Delimiter::Parenthesis,
                range,
                actual,
            );
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close_for(
                    committed,
                    ConstructRole::StructTupleFields,
                    Delimiter::Parenthesis,
                );
                break;
            }
            let trivia = committed.probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if let Some(semicolon) = committed.probe(|probe| scan_struct_semicolon(probe.input())) {
            emit_struct_error(
                committed,
                crate::session::StructRole::FieldSeparator,
                semicolon,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close_for(
                    committed,
                    ConstructRole::StructTupleFields,
                    Delimiter::Parenthesis,
                );
                break;
            }
            let trivia = committed.probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        emit_struct_missing_close_for(
            committed,
            ConstructRole::StructTupleFields,
            Delimiter::Parenthesis,
        );
        break;
    }

    committed.probe(|probe| {
        let i = probe.input();
        pop_struct_layout(layout, i);
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    });
    let _ = open;
}

fn commit_empty_struct_tuple_field<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::StructField);
    let _ = commit_direct_type_expression_with_outer_missing_role(
        Some(GrammarRole::Declaration(DeclarationRole::Struct(
            crate::session::StructRole::FieldType,
        ))),
        committed,
    );
    committed.finish_node();
}

fn commit_struct_tuple_field<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::StructField);
    let _ = commit_direct_type_expression_with_outer_missing_role(
        Some(GrammarRole::Declaration(DeclarationRole::Struct(
            crate::session::StructRole::FieldType,
        ))),
        committed,
    );
    committed.finish_node();
}

#[derive(Clone)]
enum StructBodyStarter {
    Bodyless(Range<usize>),
    NamedBraced(Range<usize>),
    Tuple(Range<usize>),
    NamedIndented(Range<usize>),
}

fn struct_body_starter<E>(i: &mut SynIn<E>) -> Option<StructBodyStarter>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    let starter = match punctuation.kind() {
        PunctuationKind::Semicolon => StructBodyStarter::Bodyless(punctuation.range()),
        PunctuationKind::Open(Delimiter::Brace) => StructBodyStarter::NamedBraced(punctuation.range()),
        PunctuationKind::Open(Delimiter::Parenthesis) => StructBodyStarter::Tuple(punctuation.range()),
        PunctuationKind::Colon => StructBodyStarter::NamedIndented(punctuation.range()),
        _ => {
            i.rollback(checkpoint);
            return None;
        }
    };
    i.rollback(checkpoint);
    Some(starter)
}

fn struct_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    struct_body_starter(i).is_some()
}

fn commit_mod_colon_body<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    mod_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    let trivia = committed.probe(|probe| probe.input().run(scan_trivia)).expect("trivia is total");
    let newline = committed.probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
    if newline && committed.probe(|probe| probe.input().local.line().line_indent <= mod_base) {
        committed.probe(|probe| probe.input().rollback(checkpoint));
        emit_mod_missing(committed, ModRole::Body, ExpectedSyntax::Statement);
        return;
    }
    if newline {
        let indent = committed.probe(|probe| probe.input().local.line().line_indent);
        commit_indented_mod_body(
            operators, trivia, mod_base, indent, committed,
        );
        return;
    }
    committed.emit_trivia(&trivia);
    commit_mod_inline_colon_body(operators, committed);
}

fn commit_mod_inline_colon_body<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let ambient_scope = committed.probe(|probe| {
        probe
            .input()
            .local
            .push_inline_canonical_statement_ambient_scope(
                crate::session::InlineStatementOwnerKind::ModColonBody,
            )
    });
    let mut statement_committed = commit_canonical_statement(operators, LeadingTrivia::None, committed);
    if !statement_committed {
        match mod_body_error_retry(operators, committed) {
            Some(true) => {
                commit_canonical_statement(operators, LeadingTrivia::None, committed)
                    .then_some(())
                    .expect("a retried Mod colon body must commit");
                statement_committed = true;
            }
            Some(false) => {}
            None => {
                emit_mod_missing(committed, ModRole::Body, ExpectedSyntax::Statement);
            }
        }
    }
    if statement_committed && let Some(semicolon) = commit_character(committed, ';') {
        committed.token(SyntaxKind::Semicolon, semicolon);
    }
    committed.probe(|probe| {
        assert_eq!(
            probe.input().local.pop_ambient_owner_scope(),
            Some(ambient_scope),
        );
    });
}

fn commit_mod_inline_statement<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let ambient_scope = committed.probe(|probe| {
        probe
            .input()
            .local
            .push_inline_canonical_statement_ambient_scope(
                crate::session::InlineStatementOwnerKind::ModColonBody,
            )
    });
    let committed_statement = commit_canonical_statement(operators, LeadingTrivia::None, committed);
    committed.probe(|probe| {
        assert_eq!(
            probe.input().local.pop_ambient_owner_scope(),
            Some(ambient_scope),
        );
    });
    committed_statement
}

fn commit_binding_body<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    binding_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<ParsedBindingBody<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let body_start = committed.probe(|probe| probe.input().pos());
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    let trivia = committed.probe(|probe| probe.input().run(scan_trivia)).expect("trivia is total");
    let has_newline = committed.probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
    if has_newline && committed.probe(|probe| probe.input().local.line().line_indent <= binding_base) {
        committed.probe(|probe| probe.input().rollback(checkpoint));
        emit_binding_missing(committed, BindingRole::Body, ExpectedSyntax::Expression);
        return Recovered::Incomplete;
    }
    if has_newline {
        let block_indent = committed.probe(|probe| probe.input().local.line().line_indent);
        commit_indented_binding_body(operators, trivia, binding_base, block_indent, committed);
        let end = committed.probe(|probe| probe.input().pos());
        return Recovered::Complete(ParsedBindingBody::new(body_start..end));
    }
    let leading = if trivia.is_empty() { LeadingTrivia::None } else { LeadingTrivia::Present };
    committed.emit_trivia(&trivia);
    let body = parse_direct_expression_with_operators(operators, leading, committed)
        .or_else(|| {
            direct_expression_error_retry(
                operators,
                GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Body)),
                committed,
            ).then(|| parse_direct_expression_with_operators(operators, LeadingTrivia::None, committed)).flatten()
        });
    match body {
        Some(body) => Recovered::Complete(ParsedBindingBody::new(body.range())),
        None => {
            emit_binding_missing(committed, BindingRole::Body, ExpectedSyntax::Expression);
            Recovered::Incomplete
        }
    }
}

/// Emits the recovery record shared by every missing inline separator. The
/// following slot remains at the current source position; no synthetic trivia
/// token is introduced.
fn emit_layout_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Layout(LayoutRole::InlineTrivia);
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::InlineTrivia,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn commit_word_candidate<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let candidate = i.run(scan_word).is_some();
        i.rollback(checkpoint);
        candidate
    })
}

fn commit_character_candidate<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    expected: char,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let candidate = scan_character(i, expected).is_some();
        i.rollback(checkpoint);
        candidate
    })
}

/// The direct Pratt parser leaves a non-NUD byte untouched on rejection.
/// Consume the invalid run as one Error episode and retry the same mandatory
/// expression slot only when a later local NUD candidate is found. Newline,
/// semicolon, and EOF remain owner boundaries and are never consumed here.
fn direct_expression_error_retry<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    role: GrammarRole,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let range = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let boundary = {
                let i = probe.input();
                let Some(character) = i.input.remainder().chars().next() else {
                    return (start < end).then_some((start..end, false));
                };
                matches!(character, '\r' | '\n' | ';')
            };
            if boundary {
                return (start < end).then_some((start..end, false));
            }
            {
                let i = probe.input();
                i.input.next()?;
                end = i.pos();
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            if crate::grammar::expression::direct_expression_nud_candidate(
                operators,
                LeadingTrivia::None,
                probe,
            ) {
                return Some((start..end, true));
            }
        }
    });
    let Some((range, retry)) = range else {
        return false;
    };
    let record = committed.probe(|probe| {
        let i = probe.input();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Expression,
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
    retry
}

fn direct_expression_candidate<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    leading: LeadingTrivia,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        crate::grammar::expression::direct_expression_nud_candidate(operators, leading, probe)
    })
}

fn emit_binding_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: BindingRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let grammar_role = GrammarRole::Declaration(DeclarationRole::Binding(role));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role: grammar_role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role: grammar_role,
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_mod_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: ModRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let grammar_role = GrammarRole::Declaration(DeclarationRole::Mod(role));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role: grammar_role, range: at..at },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role: grammar_role,
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_mod_body_introducer_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Declaration(DeclarationRole::Mod(ModRole::BodyIntroducer));
        let source = ExpectationSources::COMMITTED_RECOVERY_RULE;
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role, range: at..at },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([
                SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Semicolon), range: at..at, sources: source },
                SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(Delimiter::Brace)), range: at..at, sources: source },
                SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon), range: at..at, sources: source },
            ]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_struct_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: crate::session::StructRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Struct(role));
        let at = i.pos();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role, range: at..at },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_struct_body_introducer_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Declaration(DeclarationRole::Struct(
            crate::session::StructRole::BodyIntroducer,
        ));
        let source = ExpectationSources::COMMITTED_RECOVERY_RULE;
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role, range: at..at },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([
                SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Semicolon), range: at..at, sources: source },
                SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(Delimiter::Brace)), range: at..at, sources: source },
                SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(Delimiter::Parenthesis)), range: at..at, sources: source },
                SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon), range: at..at, sources: source },
            ]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn struct_name_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    struct_error_retry(
        committed,
        crate::session::StructRole::Name,
        ExpectedSyntax::Identifier,
        |i| struct_body_starter_pending(i),
        |i| struct_word_pending(i),
        |_| false,
    )
}

fn struct_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    struct_error_retry(
        committed,
        crate::session::StructRole::BodyIntroducer,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
        |_| false,
        |i| struct_body_starter_pending(i),
        |i| struct_word_pending(i) || struct_double_colon_pending(i),
    )
}

fn struct_word_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_word).is_some();
    i.rollback(checkpoint);
    pending
}

fn struct_double_colon_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i
        .run(scan_punctuation)
        .is_some_and(|punctuation| punctuation.kind() == PunctuationKind::ColonColon);
    i.rollback(checkpoint);
    pending
}

fn struct_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: crate::session::StructRole,
    expected: ExpectedSyntax,
    safe_boundary: impl Fn(&mut SynIn<E>) -> bool,
    retry_after_error: impl Fn(&mut SynIn<E>) -> bool,
    terminal_candidate: impl Fn(&mut SynIn<E>) -> bool,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let i = probe.input();
            let Some(character) = i.input.remainder().chars().next() else {
                return (start < end).then_some((start..end, false));
            };
            if matches!(character, '\r' | '\n' | ';' | ',' | ')' | ']' | '}')
                || safe_boundary(i)
                || terminal_candidate(i)
            {
                return (start < end).then_some((start..end, false));
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            if retry_after_error(i) {
                return Some((start..end, true));
            }
        }
    })?;
    let (range, retry) = recovered;
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Struct(role));
        let source = ExpectationSources::COMMITTED_RECOVERY_RULE;
        let expectations: Arc<[SyntaxExpectation]> = match role {
            GrammarRole::Declaration(DeclarationRole::Struct(
                crate::session::StructRole::BodyIntroducer,
            )) => Arc::from([
                SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Semicolon), range: range.clone(), sources: source },
                SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(Delimiter::Brace)), range: range.clone(), sources: source },
                SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(Delimiter::Parenthesis)), range: range.clone(), sources: source },
                SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon), range: range.clone(), sources: source },
            ]),
            _ => Arc::from([SyntaxExpectation {
                role,
                expected,
                range: range.clone(),
                sources: source,
            }]),
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role, range: range.clone() },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
            expectations,
            0,
        )
    });
    committed.emit_error(record);
    Some(retry)
}

/// Recover one malformed raw-name episode without stealing a Mod body starter
/// or a caller-owned statement boundary.  The caller decides whether a later
/// raw word is a first name or a test-module second name.
fn mod_word_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: ModRole,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let i = probe.input();
            let Some(character) = i.input.remainder().chars().next() else {
                return (start < end).then_some((start..end, false));
            };
            if matches!(character, '\r' | '\n' | ';' | ',' | ')' | ']' | '}')
                || matches!(character, '{' | ':')
            {
                return (start < end).then_some((start..end, false));
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            let checkpoint = i.checkpoint();
            let candidate = i.run(scan_word).is_some();
            i.rollback(checkpoint);
            if candidate {
                return Some((start..end, true));
            }
        }
    })?;
    let (range, retry) = recovered;
    let record = committed.probe(|probe| {
        let i = probe.input();
        let grammar_role = GrammarRole::Declaration(DeclarationRole::Mod(role));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role: grammar_role, range: range.clone() },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([SyntaxExpectation {
                role: grammar_role,
                expected: ExpectedSyntax::Identifier,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
    Some(retry)
}

/// Keep a malformed Mod body-introducer episode local.  A subsequent body
/// starter or canonical statement remains at the same position for the Mod
/// continuation; caller-owned boundaries are deliberately left untouched.
fn mod_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let character = probe.input().input.remainder().chars().next()?;
            if matches!(character, '\r' | '\n' | ';' | ',' | ')' | ']' | '}' | '{' | ':') {
                return (start < end).then_some((start..end, false));
            }
            {
                let i = probe.input();
                i.input.next()?;
                end = i.pos();
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            if crate::grammar::expression::direct_canonical_statement_candidate(
                operators,
                LeadingTrivia::None,
                probe,
            ) {
                return Some((start..end, true));
            }
        }
    })?;
    let (range, retry) = recovered;
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Mod(ModRole::BodyIntroducer));
        let source = ExpectationSources::COMMITTED_RECOVERY_RULE;
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role, range: range.clone() },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([
                SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Semicolon), range: range.clone(), sources: source },
                SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(Delimiter::Brace)), range: range.clone(), sources: source },
                SyntaxExpectation { role, expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon), range, sources: source },
            ]),
            0,
        )
    });
    committed.emit_error(record);
    Some(retry)
}

/// Recover one malformed inline colon-body episode without consuming the
/// caller's statement boundary.  A subsequent canonical statement retries
/// the same body slot.
fn mod_body_error_retry<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let character = probe.input().input.remainder().chars().next()?;
            if matches!(character, '\r' | '\n' | ';' | ',' | ')' | ']' | '}' | '{' | ':') {
                return (start < end).then_some((start..end, false));
            }
            {
                let i = probe.input();
                i.input.next()?;
                end = i.pos();
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            if crate::grammar::expression::direct_canonical_statement_candidate(
                operators,
                LeadingTrivia::None,
                probe,
            ) {
                return Some((start..end, true));
            }
        }
    })?;
    let (range, retry) = recovered;
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Mod(ModRole::Body));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role, range: range.clone() },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Statement,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
    Some(retry)
}

/// Emits the common committed-recovery shape for an import-owned mandatory
/// slot.  Use continuations select the narrow `ImportRole` at their call site;
/// the record construction itself stays shared with every such slot.
fn emit_import_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: ImportRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let grammar_role = GrammarRole::Declaration(DeclarationRole::Import(role));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role: grammar_role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role: grammar_role,
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_import_group_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    delimiter: Delimiter,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::ClosingDelimiter {
            owner: ConstructRole::ImportGroup,
            delimiter,
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    delimiter,
                )),
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_import_group_mismatched_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
    actual: Delimiter,
    expected: Delimiter,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::ClosingDelimiter {
            owner: ConstructRole::ImportGroup,
            delimiter: expected,
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::Punctuation(
                    crate::session::PunctuationEvidence::Close(actual),
                ),
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    expected,
                )),
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn emit_import_operator_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::ClosingDelimiter {
            owner: ConstructRole::OperatorName,
            delimiter: Delimiter::Parenthesis,
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    Delimiter::Parenthesis,
                )),
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

/// Completes an accepted operator-header introduction while building its AST
/// and direct CST from the same scans.
pub(crate) fn commit_operator_header<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: OperatorStatementIntro<'source>,
) -> Recovered<OperatorHeaderDeclaration<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::OperatorHeader);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    if let Some(lazy_keyword) = intro.lazy_keyword {
        committed.token(SyntaxKind::LazyKw, lazy_keyword.range());
        if let Some(trivia) = &intro.after_lazy {
            committed.emit_trivia(trivia);
        } else if commit_operator_fixity_candidate(committed) {
            emit_layout_missing(committed);
        }
    }
    let fixity = match intro.fixity_keyword {
        Some(keyword) => {
            let fixity = parse_operator_fixity(keyword)
                .expect("operator intro stores only a recognized fixity");
            committed.token(fixity_token_kind(fixity), keyword.range());
            Recovered::Complete(fixity)
        }
        None => commit_operator_fixity(committed),
    };
    let fixity = match fixity {
        Recovered::Complete(fixity) => fixity,
        Recovered::Incomplete => {
            committed.finish_node();
            return Recovered::Incomplete;
        }
    };

    if let Some(trivia) = &intro.after_fixity {
        committed.emit_trivia(trivia);
    } else {
        emit_optional_inline_trivia(committed);
    }
    let name = match commit_operator_name(committed) {
        Recovered::Complete(name) => Some(name),
        Recovered::Incomplete => None,
    };
    let (left_binding_power, right_binding_power, binding_powers_complete) = match fixity {
        OperatorFixity::Nullfix => (None, None, true),
        OperatorFixity::Prefix => {
            emit_optional_inline_trivia(committed);
            let right = commit_binding_power(committed, OperatorHeaderRole::RightBindingPower);
            let complete = matches!(right, Recovered::Complete(_));
            (None, recovered_binding_power(right), complete)
        }
        OperatorFixity::Suffix => {
            emit_optional_inline_trivia(committed);
            let left = commit_binding_power(committed, OperatorHeaderRole::LeftBindingPower);
            let complete = matches!(left, Recovered::Complete(_));
            (recovered_binding_power(left), None, complete)
        }
        OperatorFixity::Infix => {
            emit_optional_inline_trivia(committed);
            let left = commit_binding_power(committed, OperatorHeaderRole::LeftBindingPower);
            emit_optional_inline_trivia(committed);
            let right = commit_binding_power(committed, OperatorHeaderRole::RightBindingPower);
            let complete =
                matches!(left, Recovered::Complete(_)) && matches!(right, Recovered::Complete(_));
            (
                recovered_binding_power(left),
                recovered_binding_power(right),
                complete,
            )
        }
    };
    emit_optional_inline_trivia(committed);
    let equals = commit_operator_definition_introducer(committed);
    committed.finish_node();

    match (name, binding_powers_complete, equals) {
        (Some(name), true, Recovered::Complete(equals)) => {
            Recovered::Complete(OperatorHeaderDeclaration {
                range: intro.start..equals.end,
                name,
                visibility: intro
                    .visibility
                    .as_ref()
                    .map_or(Visibility::Private, |prefix| prefix.visibility),
                lazy: intro.lazy_keyword.is_some(),
                fixity,
                left_binding_power,
                right_binding_power,
            })
        }
        _ => Recovered::Incomplete,
    }
}

/// Continues a complete [`commit_operator_header`] in a full parse session.
///
/// The header has already closed its `OperatorHeader` node and produced its
/// header fact before this function starts.  Consequently a missing or
/// malformed body can only produce the full-origin body recovery below; it
/// cannot retract or alter that fact.  The future root driver calls this only
/// after `commit_operator_header` returned [`Recovered::Complete`].
pub(crate) fn commit_operator_definition_body<'parse, 'source, 'local, E>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, FullCstOutput<'source>>,
) -> Recovered<ParsedExpression<rowan::Checkpoint>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let after_equals = commit_required_inline_trivia(committed);
    let leading = if after_equals.as_ref().is_none_or(TriviaRun::is_empty) {
        LeadingTrivia::None
    } else {
        LeadingTrivia::Present
    };
    if let Some(after_equals) = &after_equals {
        committed.emit_trivia(after_equals);
    }
    if after_equals.as_ref().is_none_or(TriviaRun::is_empty)
        && direct_expression_candidate(operators, leading, committed)
    {
        emit_layout_missing(committed);
    }

    if let Some(body) = parse_direct_expression_with_operators(operators, leading, committed) {
        return Recovered::Complete(body);
    }
    if direct_expression_error_retry(
        operators,
        GrammarRole::Statement(StatementRole::OperatorDefinitionBody),
        committed,
    ) {
        if let Some(body) =
            parse_direct_expression_with_operators(operators, LeadingTrivia::None, committed)
        {
            return Recovered::Complete(body);
        }
    }

    emit_operator_definition_body_missing(committed);
    Recovered::Incomplete
}

fn emit_operator_definition_body_missing<'parse, 'source, 'local, E>(
    committed: &mut Committed<'parse, 'source, 'local, E, FullCstOutput<'source>>,
) where
    E: ErrorSink<usize>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Statement(StatementRole::OperatorDefinitionBody);
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Expression,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn recovered_binding_power(value: Recovered<BindingPower>) -> Option<BindingPower> {
    match value {
        Recovered::Complete(value) => Some(value),
        Recovered::Incomplete => None,
    }
}

fn fixity_token_kind(fixity: OperatorFixity) -> SyntaxKind {
    match fixity {
        OperatorFixity::Prefix => SyntaxKind::PrefixKw,
        OperatorFixity::Infix => SyntaxKind::InfixKw,
        OperatorFixity::Suffix => SyntaxKind::SuffixKw,
        OperatorFixity::Nullfix => SyntaxKind::NullfixKw,
    }
}

fn commit_operator_fixity<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<OperatorFixity>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if !commit_operator_fixity_candidate(committed) && !operator_fixity_error_retry(committed) {
        emit_operator_fixity_missing(committed);
        return Recovered::Incomplete;
    }
    let keyword = commit_word(committed).expect("sink-free candidate must still scan a word");
    let fixity = parse_operator_fixity(keyword).expect("candidate recognizes only a fixity");
    committed.token(fixity_token_kind(fixity), keyword.range());
    Recovered::Complete(fixity)
}

/// Fixity is the header shape discriminator.  A malformed spelling owns one
/// Error episode and may retry only at a later recognized discriminator;
/// otherwise the continuation stops without inventing a BP arity.
fn operator_fixity_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let i = probe.input();
            let Some(character) = i.input.remainder().chars().next() else {
                return (start < end).then_some((start..end, false));
            };
            if matches!(character, '\r' | '\n' | ';') {
                return (start < end).then_some((start..end, false));
            }
            let checkpoint = i.checkpoint();
            let candidate = i.run(scan_word).and_then(parse_operator_fixity).is_some();
            i.rollback(checkpoint);
            if candidate {
                return (start < end).then_some((start..end, true));
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    });
    let Some((range, retry)) = recovered else {
        return false;
    };
    emit_operator_error(
        committed,
        OperatorHeaderRole::Fixity,
        ExpectedSyntax::Keyword(crate::session::KeywordEvidence::Prefix),
        range,
        crate::session::UnexpectedCategory::Word,
    );
    retry
}

fn commit_operator_fixity_candidate<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let candidate = i.run(scan_word).and_then(parse_operator_fixity).is_some();
        i.rollback(checkpoint);
        candidate
    })
}

fn emit_operator_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: OperatorHeaderRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let grammar_role = GrammarRole::Declaration(DeclarationRole::OperatorHeader(role));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role: grammar_role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role: grammar_role,
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_operator_fixity_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role =
            GrammarRole::Declaration(DeclarationRole::OperatorHeader(OperatorHeaderRole::Fixity));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Keyword(crate::session::KeywordEvidence::Prefix),
                    range: at..at,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Keyword(crate::session::KeywordEvidence::Infix),
                    range: at..at,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Keyword(crate::session::KeywordEvidence::Suffix),
                    range: at..at,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Keyword(crate::session::KeywordEvidence::Nullfix),
                    range: at..at,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                },
            ]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_operator_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: OperatorHeaderRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
    category: crate::session::UnexpectedCategory,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let grammar_role = GrammarRole::Declaration(DeclarationRole::OperatorHeader(role));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role: grammar_role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category,
            }]),
            Arc::from([SyntaxExpectation {
                role: grammar_role,
                expected,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn emit_operator_name_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::ClosingDelimiter {
            owner: ConstructRole::OperatorName,
            delimiter: Delimiter::Parenthesis,
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    Delimiter::Parenthesis,
                )),
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn commit_operator_definition_introducer<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(equals) = commit_character(committed, '=') {
        committed.token(SyntaxKind::Equals, equals.clone());
        return Recovered::Complete(equals);
    }
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let i = probe.input();
            let Some(character) = i.input.remainder().chars().next() else {
                return (start < end).then_some(start..end);
            };
            if matches!(character, '\r' | '\n' | ';' | '=') {
                return (start < end).then_some(start..end);
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    });
    if let Some(range) = recovered {
        emit_operator_error(
            committed,
            OperatorHeaderRole::DefinitionIntroducer,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Equals),
            range,
            crate::session::UnexpectedCategory::OtherCharacter,
        );
        if let Some(equals) = commit_character(committed, '=') {
            committed.token(SyntaxKind::Equals, equals.clone());
            // The punctuation is present after an Error episode, but that
            // episode means this mandatory slot cannot contribute a complete
            // header fact.
            return Recovered::Incomplete;
        }
    }
    emit_operator_missing(
        committed,
        OperatorHeaderRole::DefinitionIntroducer,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Equals),
    );
    Recovered::Incomplete
}

fn commit_operator_name<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<&'source str>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::OperatorName);
    let open = if let Some(open) = commit_character(committed, '(') {
        committed.token(SyntaxKind::LParen, open);
        true
    } else {
        emit_operator_missing(
            committed,
            OperatorHeaderRole::Name,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(
                Delimiter::Parenthesis,
            )),
        );
        false
    };
    if !open {
        committed.finish_node();
        return Recovered::Incomplete;
    }

    let spelling = committed.probe(|probe| {
        let i = probe.input();
        let start = i.pos();
        while let Some(character) = i.input.remainder().chars().next() {
            if character == ')' {
                break;
            }
            if character.is_whitespace()
                || matches!(
                    character,
                    '(' | '[' | ']' | '{' | '}' | '\\' | ',' | ';' | '"' | '\''
                )
            {
                break;
            }
            i.input.next()?;
        }
        let end = i.pos();
        (start < end).then_some((&i.input.source()[start..end], start..end))
    });
    let Some((name, range)) = spelling else {
        emit_operator_missing(
            committed,
            OperatorHeaderRole::Name,
            ExpectedSyntax::OperatorName,
        );
        if let Some(close) = commit_character(committed, ')') {
            committed.token(SyntaxKind::RParen, close);
        } else {
            emit_operator_name_close_missing(committed);
        }
        committed.finish_node();
        return Recovered::Incomplete;
    };
    committed.token(SyntaxKind::Operator, range);
    let close = if let Some(close) = commit_character(committed, ')') {
        committed.token(SyntaxKind::RParen, close);
        true
    } else {
        emit_operator_name_close_missing(committed);
        false
    };
    committed.finish_node();
    close
        .then_some(name)
        .map_or(Recovered::Incomplete, Recovered::Complete)
}

fn commit_binding_power<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: OperatorHeaderRole,
) -> Recovered<BindingPower>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    enum BindingPowerScan {
        Complete(BindingPower, Vec<Range<usize>>, Vec<Range<usize>>),
        Invalid(Range<usize>),
    }

    let scan = committed.probe(|probe| {
        let i = probe.input();
        let mut values = Vec::new();
        let mut components = Vec::new();
        let mut dots = Vec::new();
        let start = i.pos();

        loop {
            let component_start = i.pos();
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
            if component_start == end {
                return (start < end).then_some(BindingPowerScan::Invalid(start..end));
            }
            let Ok(value) = i.input.source()[component_start..end].parse::<i8>() else {
                return Some(BindingPowerScan::Invalid(start..end));
            };
            values.push(value);
            components.push(component_start..end);

            if !i.input.remainder().starts_with('.') {
                break;
            }
            dots.push(scan_character(i, '.')?);
        }

        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        let (first, rest) = values.split_first()?;
        Some(BindingPowerScan::Complete(
            BindingPower::new(*first, rest.iter().copied()),
            components,
            dots,
        ))
    });

    match scan {
        Some(BindingPowerScan::Complete(binding_power, components, dots)) => {
            committed.start_node(SyntaxKind::BindingPower);
            for (index, component) in components.into_iter().enumerate() {
                if index > 0 {
                    committed.token(SyntaxKind::Dot, dots[index - 1].clone());
                }
                committed.token(SyntaxKind::Integer, component);
            }
            committed.finish_node();
            Recovered::Complete(binding_power)
        }
        Some(BindingPowerScan::Invalid(range)) => {
            emit_operator_error(
                committed,
                role,
                ExpectedSyntax::BindingPower,
                range,
                crate::session::UnexpectedCategory::DecimalInteger,
            );
            Recovered::Incomplete
        }
        None => {
            if binding_power_error_retry(committed, role) {
                commit_binding_power(committed, role)
            } else {
                emit_operator_missing(committed, role, ExpectedSyntax::BindingPower);
                Recovered::Incomplete
            }
        }
    }
}

/// A binding-power slot retries only at a later digit vector.  Words are a
/// body-NUD safe point, so they stay for the operator-definition continuation
/// rather than becoming a fabricated binding power here.
fn binding_power_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: OperatorHeaderRole,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let i = probe.input();
            let Some(character) = i.input.remainder().chars().next() else {
                return (start < end).then_some((start..end, false));
            };
            if matches!(character, '\r' | '\n' | ';' | '=') {
                return (start < end).then_some((start..end, false));
            }
            if character.is_ascii_digit() {
                return (start < end).then_some((start..end, true));
            }
            let checkpoint = i.checkpoint();
            let body_nud = i.run(scan_word).is_some();
            i.rollback(checkpoint);
            if body_nud {
                return (start < end).then_some((start..end, false));
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    });
    let Some((range, retry)) = recovered else {
        return false;
    };
    emit_operator_error(
        committed,
        role,
        ExpectedSyntax::BindingPower,
        range,
        crate::session::UnexpectedCategory::OtherCharacter,
    );
    retry
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
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(trivia) = commit_optional_inline_trivia(committed) {
        committed.emit_trivia(&trivia);
    }
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
) -> Recovered<UseDeclaration<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::UseDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::UseKw, intro.use_keyword.range());
    if let Some(trivia) = &intro.after_use {
        committed.emit_trivia(trivia);
    } else if commit_use_tree_candidate(committed) {
        emit_layout_missing(committed);
    }
    if !commit_use_tree_candidate(committed) && !use_tree_error_retry(committed) {
        emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::Path);
        committed.finish_node();
        return Recovered::Incomplete;
    }
    let tree = match commit_use_tree(committed) {
        Recovered::Complete(tree) => tree,
        Recovered::Incomplete => {
            committed.finish_node();
            return Recovered::Incomplete;
        }
    };
    committed.finish_node();

    Recovered::Complete(UseDeclaration {
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
) -> Recovered<UseTree<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = committed_position(committed);
    committed.start_node(SyntaxKind::UseTree);

    let (form, prefix, terminal, terminal_end, glob_aliases) = if let Some(open) =
        commit_maybe_character(committed, '{').flatten()
    {
        let (terminal, end) = match commit_use_group(committed, open) {
            Recovered::Complete(group) => group,
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        };
        (
            HeaderImportForm::Plain,
            empty_use_path(),
            terminal,
            end,
            Vec::new(),
        )
    } else if let Some(open) = commit_maybe_character(committed, '(').flatten() {
        let first = match commit_parenthesized_use_operator(committed, open) {
            Recovered::Complete(segment) => segment,
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        };
        match commit_use_path_and_terminal(committed, first, None, HeaderImportForm::Plain) {
            Recovered::Complete(result) => result,
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        }
    } else {
        let Some(first) = commit_word(committed) else {
            emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::Path);
            committed.finish_node();
            return Recovered::Incomplete;
        };
        if first.text() == "mod" {
            committed.token(SyntaxKind::ModKw, first.range());
            if let Some(trivia) = commit_required_inline_trivia(committed) {
                committed.emit_trivia(&trivia);
            } else if commit_word_candidate(committed) {
                emit_layout_missing(committed);
            }
            let Some(first_segment) = commit_word(committed).map(UseSegment::Word) else {
                emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::Identifier);
                committed.finish_node();
                return Recovered::Incomplete;
            };
            match commit_use_path_and_terminal(
                committed,
                first_segment,
                None,
                HeaderImportForm::Mod,
            ) {
                Recovered::Complete(result) => result,
                Recovered::Incomplete => {
                    committed.finish_node();
                    return Recovered::Incomplete;
                }
            }
        } else {
            let following_separator = commit_maybe_use_separator(committed).flatten();
            let form = classify_use_form(
                first,
                following_separator
                    .as_ref()
                    .map(|(separator, _)| *separator),
            );
            match form {
                HeaderImportForm::Plain => match commit_use_path_and_terminal(
                    committed,
                    UseSegment::Word(first),
                    following_separator,
                    HeaderImportForm::Plain,
                ) {
                    Recovered::Complete(result) => result,
                    Recovered::Incomplete => {
                        committed.finish_node();
                        return Recovered::Incomplete;
                    }
                },
                HeaderImportForm::Realm | HeaderImportForm::Band => {
                    committed.token(
                        if form == HeaderImportForm::Realm {
                            SyntaxKind::RealmKw
                        } else {
                            SyntaxKind::BandKw
                        },
                        first.range(),
                    );
                    let (_, marker_range) = following_separator
                        .expect("realm and band forms require their marker separator");
                    committed.token(
                        separator_token_kind(form_marker_separator(form)),
                        marker_range,
                    );
                    if let Some(open) = commit_maybe_character(committed, '{').flatten() {
                        let (terminal, end) = match commit_use_group(committed, open) {
                            Recovered::Complete(group) => group,
                            Recovered::Incomplete => {
                                committed.finish_node();
                                return Recovered::Incomplete;
                            }
                        };
                        (form, empty_use_path(), terminal, end, Vec::new())
                    } else if let Some(star) = commit_maybe_character(committed, '*').flatten() {
                        let (terminal, end, aliases) = match commit_use_glob(committed, star) {
                            Recovered::Complete(glob) => glob,
                            Recovered::Incomplete => {
                                committed.finish_node();
                                return Recovered::Incomplete;
                            }
                        };
                        (form, empty_use_path(), terminal, end, aliases)
                    } else {
                        let first_segment = match commit_use_path_segment(committed) {
                            Recovered::Complete(segment) => segment,
                            Recovered::Incomplete => {
                                committed.finish_node();
                                return Recovered::Incomplete;
                            }
                        };
                        match commit_use_path_and_terminal(committed, first_segment, None, form) {
                            Recovered::Complete(result) => result,
                            Recovered::Incomplete => {
                                committed.finish_node();
                                return Recovered::Incomplete;
                            }
                        }
                    }
                }
                HeaderImportForm::Mod => {
                    unreachable!("mod was handled before marker classification")
                }
            }
        }
    };

    let aliases = match terminal {
        UseTerminal::Glob { .. } => glob_aliases,
        _ => match commit_use_aliases(committed) {
            Recovered::Complete(aliases) => aliases,
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        },
    };
    let qualifiers = match commit_use_qualifiers(committed) {
        Recovered::Complete(qualifiers) => qualifiers,
        Recovered::Incomplete => {
            committed.finish_node();
            return Recovered::Incomplete;
        }
    };
    let end = qualifiers_end(&qualifiers).unwrap_or_else(|| {
        aliases
            .last()
            .map_or(terminal_end, |alias| alias.range().end)
    });
    committed.finish_node();

    Recovered::Complete(UseTree {
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
        HeaderImportForm::Plain | HeaderImportForm::Mod => {
            unreachable!("only markers have a marker separator")
        }
    }
}

fn commit_use_path_and_terminal<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    first: UseSegment<'source>,
    mut pending_separator: Option<(UseSeparator, Range<usize>)>,
    form: HeaderImportForm,
) -> Recovered<(
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
            .or(commit_maybe_use_separator(committed).flatten())
        else {
            committed.finish_node();
            let end = path
                .segments()
                .last()
                .expect("use path has its first segment")
                .range()
                .end;
            return Recovered::Complete((form, path, UseTerminal::Single, end, Vec::new()));
        };
        if let Some(open) = commit_maybe_character(committed, '{').flatten() {
            committed.finish_node();
            committed.token(separator_token_kind(separator), range);
            let (terminal, end) = match commit_use_group(committed, open) {
                Recovered::Complete(group) => group,
                Recovered::Incomplete => return Recovered::Incomplete,
            };
            return Recovered::Complete((
                form,
                path,
                terminal_with_join(terminal, separator),
                end,
                Vec::new(),
            ));
        }
        if let Some(star) = commit_maybe_character(committed, '*').flatten() {
            committed.finish_node();
            committed.token(separator_token_kind(separator), range);
            let (terminal, end, aliases) = match commit_use_glob(committed, star) {
                Recovered::Complete(glob) => glob,
                Recovered::Incomplete => return Recovered::Incomplete,
            };
            return Recovered::Complete((
                form,
                path,
                terminal_with_join(terminal, separator),
                end,
                aliases,
            ));
        }
        committed.token(separator_token_kind(separator), range);
        path.separators.push(separator);
        let segment = match commit_use_path_segment(committed) {
            Recovered::Complete(segment) => segment,
            Recovered::Incomplete => {
                emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::Path);
                committed.finish_node();
                return Recovered::Incomplete;
            }
        };
        emit_use_segment(committed, &segment);
        path.segments.push(segment);
    }
}

fn terminal_with_join<'source>(
    terminal: UseTerminal<'source>,
    join: UseSeparator,
) -> UseTerminal<'source> {
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
) -> Recovered<UseSegment<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(open) = commit_maybe_character(committed, '(').flatten() {
        return commit_parenthesized_use_operator(committed, open);
    }
    match commit_word(committed) {
        Some(word) => Recovered::Complete(UseSegment::Word(word)),
        None => {
            emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::Path);
            Recovered::Incomplete
        }
    }
}

/// Once `(` selects an operator segment, it owns the operator-name node.  A
/// malformed spelling or absent `)` therefore cannot fall back into a group
/// arm and leave the direct CST unbalanced.
fn commit_parenthesized_use_operator<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    open: Range<usize>,
) -> Recovered<UseSegment<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let spelling = committed.probe(|probe| {
        let i = probe.input();
        let start = i.pos();
        while let Some(character) = i.input.remainder().chars().next() {
            if !is_use_operator_character(character) {
                break;
            }
            i.input.next()?;
        }
        let end = i.pos();
        (start < end).then_some(start..end)
    });
    let Some(spelling) = spelling else {
        committed.start_node(SyntaxKind::OperatorName);
        committed.token(SyntaxKind::LParen, open);
        emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::OperatorName);
        committed.finish_node();
        return Recovered::Incomplete;
    };
    let Some(close) = commit_maybe_character(committed, ')').flatten() else {
        committed.start_node(SyntaxKind::OperatorName);
        committed.token(SyntaxKind::LParen, open);
        committed.token(SyntaxKind::Operator, spelling);
        emit_import_operator_close_missing(committed);
        committed.finish_node();
        return Recovered::Incomplete;
    };
    Recovered::Complete(UseSegment::Operator {
        range: open.start..close.end,
        text: &committed.probe(|probe| probe.input().input.source())[spelling],
    })
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
            committed.token(SyntaxKind::Operator, range.start + 1..range.end - 1);
            committed.token(SyntaxKind::RParen, range.end - 1..range.end);
            committed.finish_node();
        }
    }
}

fn commit_use_group<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    open: Range<usize>,
) -> Recovered<(UseTerminal<'source>, usize)>
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
        let trivia = commit_trivia(committed).expect("trivia scanning is total");
        committed.emit_trivia(&trivia);
        if let Some(close) = commit_maybe_character(committed, '}').flatten() {
            committed.token(SyntaxKind::RBrace, close.clone());
            committed.finish_node();
            return Recovered::Complete((UseTerminal::Group { join: None, items }, close.end));
        }
        if let Some(close) = commit_maybe_character(committed, ')').flatten() {
            emit_import_group_mismatched_close(
                committed,
                close,
                Delimiter::Parenthesis,
                Delimiter::Brace,
            );
            continue;
        }
        if committed_at_eof(committed) {
            emit_import_group_close_missing(committed, Delimiter::Brace);
            committed.finish_node();
            return Recovered::Complete((
                UseTerminal::Group { join: None, items },
                committed_position(committed),
            ));
        }
        if let Recovered::Complete(item) = commit_use_tree(committed) {
            items.push(item);
        }
        let trivia = commit_trivia(committed).expect("trivia scanning is total");
        let newline = trivia_has_newline(committed, &trivia);
        committed.emit_trivia(&trivia);
        if let Some(close) = commit_maybe_character(committed, '}').flatten() {
            committed.token(SyntaxKind::RBrace, close.clone());
            committed.finish_node();
            return Recovered::Complete((UseTerminal::Group { join: None, items }, close.end));
        }
        if let Some(close) = commit_maybe_character(committed, ')').flatten() {
            emit_import_group_mismatched_close(
                committed,
                close,
                Delimiter::Parenthesis,
                Delimiter::Brace,
            );
            continue;
        }
        if let Some(comma) = commit_maybe_character(committed, ',').flatten() {
            committed.token(SyntaxKind::Comma, comma);
        } else if committed_at_eof(committed) {
            emit_import_group_close_missing(committed, Delimiter::Brace);
            committed.finish_node();
            return Recovered::Complete((
                UseTerminal::Group { join: None, items },
                committed_position(committed),
            ));
        } else if commit_use_tree_candidate(committed) {
            // Two same-line tree atoms need an explicit comma.  Keep the
            // second atom at this position so the next group iteration can
            // recover it as an ordinary sibling.
            emit_import_missing(
                committed,
                ImportRole::GroupEntry,
                ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Comma),
            );
        } else if !newline {
            emit_import_group_close_missing(committed, Delimiter::Brace);
            committed.finish_node();
            return Recovered::Complete((
                UseTerminal::Group { join: None, items },
                committed_position(committed),
            ));
        }
    }
}

fn commit_use_glob<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    star: Range<usize>,
) -> Recovered<(UseTerminal<'source>, usize, Vec<WordSpan<'source>>)>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::UseGlob);
    committed.token(SyntaxKind::Star, star.clone());
    let aliases = match commit_use_aliases(committed) {
        Recovered::Complete(aliases) => aliases,
        Recovered::Incomplete => {
            committed.finish_node();
            return Recovered::Incomplete;
        }
    };
    let mut end = aliases.last().map_or(star.end, |alias| alias.range().end);
    let mut without = Vec::new();
    if let Some(prefix) = commit_maybe_without_prefix(committed) {
        committed.emit_trivia(&prefix.leading);
        committed.token(SyntaxKind::WithoutKw, prefix.keyword.range());
        if let Some(trivia) = &prefix.after_keyword {
            committed.emit_trivia(trivia);
        } else if commit_use_exclusion_candidate(committed) {
            emit_layout_missing(committed);
        }
        match commit_use_exclusion(committed) {
            Recovered::Complete(exclusion) => {
                end = exclusion_range(&exclusion).end;
                without.push(exclusion);
            }
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        }
        while let Some(comma) = commit_maybe_character(committed, ',').flatten() {
            committed.token(SyntaxKind::Comma, comma);
            let trivia = commit_trivia(committed).expect("trivia scanning is total");
            committed.emit_trivia(&trivia);
            match commit_use_exclusion(committed) {
                Recovered::Complete(exclusion) => {
                    end = exclusion_range(&exclusion).end;
                    without.push(exclusion);
                }
                Recovered::Incomplete => break,
            }
        }
    }
    committed.finish_node();
    Recovered::Complete((
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
) -> Recovered<Vec<WordSpan<'source>>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut aliases = Vec::new();
    while let Some(alias) = commit_maybe_use_alias(committed) {
        committed.emit_trivia(&alias.leading);
        committed.start_node(SyntaxKind::UseAlias);
        committed.token(SyntaxKind::AsKw, alias.keyword.range());
        if let Some(trivia) = &alias.after_keyword {
            committed.emit_trivia(trivia);
        } else if commit_word_candidate(committed) {
            emit_layout_missing(committed);
        }
        let Some(name) = alias.name else {
            emit_import_missing(committed, ImportRole::Alias, ExpectedSyntax::Identifier);
            committed.finish_node();
            return Recovered::Incomplete;
        };
        committed.token(SyntaxKind::Identifier, name.range());
        committed.finish_node();
        aliases.push(name);
    }
    Recovered::Complete(aliases)
}

fn commit_use_qualifiers<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<UseQualifiers<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let version = commit_maybe_version(committed);
    let anchor_prefix = commit_maybe_with_prefix(committed);
    if version.is_none() && anchor_prefix.is_none() {
        return Recovered::Complete(UseQualifiers::default());
    }
    committed.start_node(SyntaxKind::UseQualifiers);
    if let Some(version) = version {
        committed.emit_trivia(&version.leading);
        committed.start_node(SyntaxKind::UseVersion);
        committed.token(SyntaxKind::Version, version.value.range());
        committed.finish_node();
        let anchor = if let Some(prefix) = anchor_prefix {
            match commit_use_anchor(committed, prefix) {
                Recovered::Complete(anchor) => Some(anchor),
                Recovered::Incomplete => {
                    committed.finish_node();
                    return Recovered::Incomplete;
                }
            }
        } else {
            None
        };
        committed.finish_node();
        return Recovered::Complete(UseQualifiers {
            version: Some(version.value),
            anchor,
        });
    }
    let anchor =
        match commit_use_anchor(committed, anchor_prefix.expect("anchor prefix was checked")) {
            Recovered::Complete(anchor) => anchor,
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        };
    committed.finish_node();
    Recovered::Complete(UseQualifiers {
        version: None,
        anchor: Some(anchor),
    })
}

fn commit_use_anchor<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    prefix: WithPrefix<'source>,
) -> Recovered<UsePath<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.emit_trivia(&prefix.leading);
    committed.start_node(SyntaxKind::UseAnchor);
    committed.token(SyntaxKind::WithKw, prefix.keyword.range());
    if let Some(trivia) = &prefix.after_keyword {
        committed.emit_trivia(trivia);
    } else if commit_word_candidate(committed) {
        emit_layout_missing(committed);
    }
    committed.start_node(SyntaxKind::UsePath);
    let Some(first) = commit_word(committed) else {
        emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::Identifier);
        committed.finish_node();
        committed.finish_node();
        return Recovered::Incomplete;
    };
    committed.token(SyntaxKind::Identifier, first.range());
    let mut path = UsePath {
        segments: vec![UseSegment::Word(first)],
        separators: Vec::new(),
    };
    while let Some((separator, range)) = commit_maybe_use_separator(committed).flatten() {
        let Some(segment) = commit_word(committed) else {
            emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::Identifier);
            committed.finish_node();
            committed.finish_node();
            return Recovered::Incomplete;
        };
        committed.token(separator_token_kind(separator), range);
        committed.token(SyntaxKind::Identifier, segment.range());
        path.separators.push(separator);
        path.segments.push(UseSegment::Word(segment));
    }
    committed.finish_node();
    committed.finish_node();
    Recovered::Complete(path)
}

fn commit_use_exclusion<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<UseExclusion<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = committed_position(committed);
    committed.start_node(SyntaxKind::UseExclusion);
    if let Some(open) = commit_maybe_character(committed, '(').flatten() {
        if commit_parenthesized_use_operator_candidate(committed) {
            let group = match commit_parenthesized_use_operator(committed, open) {
                Recovered::Complete(segment) => UseExclusion::Segment(segment),
                Recovered::Incomplete => {
                    committed.finish_node();
                    return Recovered::Incomplete;
                }
            };
            let UseExclusion::Segment(segment) = &group else {
                unreachable!("operator parsing always returns a segment");
            };
            emit_use_segment(committed, segment);
            committed.finish_node();
            return Recovered::Complete(group);
        }
        let group = match commit_use_exclusion_group(committed, open, '(', ')') {
            Recovered::Complete(group) => group,
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        };
        committed.finish_node();
        return Recovered::Complete(group);
    }
    if let Some(open) = commit_maybe_character(committed, '{').flatten() {
        let group = match commit_use_exclusion_group(committed, open, '{', '}') {
            Recovered::Complete(group) => group,
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        };
        committed.finish_node();
        return Recovered::Complete(group);
    }
    if let Some(star) = commit_maybe_character(committed, '*').flatten() {
        committed.token(SyntaxKind::Star, star.clone());
        committed.finish_node();
        return Recovered::Complete(UseExclusion::Glob { range: star });
    }
    let Some(word) = commit_word(committed) else {
        emit_import_missing(
            committed,
            ImportRole::GroupEntry,
            ExpectedSyntax::Identifier,
        );
        committed.finish_node();
        return Recovered::Incomplete;
    };
    committed.token(SyntaxKind::Identifier, word.range());
    committed.finish_node();
    debug_assert_eq!(word.range().start, start);
    Recovered::Complete(UseExclusion::Segment(UseSegment::Word(word)))
}

fn commit_use_exclusion_group<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    open: Range<usize>,
    opening: char,
    closing: char,
) -> Recovered<UseExclusion<'source>>
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
        let trivia = commit_trivia(committed).expect("trivia scanning is total");
        committed.emit_trivia(&trivia);
        if let Some(close) = commit_maybe_character(committed, closing).flatten() {
            committed.token(
                if closing == ')' {
                    SyntaxKind::RParen
                } else {
                    SyntaxKind::RBrace
                },
                close.clone(),
            );
            committed.finish_node();
            return Recovered::Complete(UseExclusion::Group {
                range: start..close.end,
                items,
            });
        }
        let mismatched = if closing == ')' { '}' } else { ')' };
        if let Some(close) = commit_maybe_character(committed, mismatched).flatten() {
            emit_import_group_mismatched_close(
                committed,
                close,
                if mismatched == ')' {
                    Delimiter::Parenthesis
                } else {
                    Delimiter::Brace
                },
                if closing == ')' {
                    Delimiter::Parenthesis
                } else {
                    Delimiter::Brace
                },
            );
            continue;
        }
        if committed_at_eof(committed) {
            let delimiter = if closing == ')' {
                Delimiter::Parenthesis
            } else {
                Delimiter::Brace
            };
            emit_import_group_close_missing(committed, delimiter);
            committed.finish_node();
            return Recovered::Complete(UseExclusion::Group {
                range: start..committed_position(committed),
                items,
            });
        }
        match commit_use_tree(committed) {
            Recovered::Complete(item) => items.push(item),
            Recovered::Incomplete => {}
        }
        let trivia = commit_trivia(committed).expect("trivia scanning is total");
        let newline = trivia_has_newline(committed, &trivia);
        committed.emit_trivia(&trivia);
        if let Some(close) = commit_maybe_character(committed, closing).flatten() {
            committed.token(
                if closing == ')' {
                    SyntaxKind::RParen
                } else {
                    SyntaxKind::RBrace
                },
                close.clone(),
            );
            committed.finish_node();
            return Recovered::Complete(UseExclusion::Group {
                range: start..close.end,
                items,
            });
        }
        let mismatched = if closing == ')' { '}' } else { ')' };
        if let Some(close) = commit_maybe_character(committed, mismatched).flatten() {
            emit_import_group_mismatched_close(
                committed,
                close,
                if mismatched == ')' {
                    Delimiter::Parenthesis
                } else {
                    Delimiter::Brace
                },
                if closing == ')' {
                    Delimiter::Parenthesis
                } else {
                    Delimiter::Brace
                },
            );
            continue;
        }
        if committed_at_eof(committed) {
            let delimiter = if closing == ')' {
                Delimiter::Parenthesis
            } else {
                Delimiter::Brace
            };
            emit_import_group_close_missing(committed, delimiter);
            committed.finish_node();
            return Recovered::Complete(UseExclusion::Group {
                range: start..committed_position(committed),
                items,
            });
        }
        if let Some(comma) = commit_maybe_character(committed, ',').flatten() {
            committed.token(SyntaxKind::Comma, comma);
        } else if !newline {
            let delimiter = if closing == ')' {
                Delimiter::Parenthesis
            } else {
                Delimiter::Brace
            };
            emit_import_group_close_missing(committed, delimiter);
            committed.finish_node();
            return Recovered::Complete(UseExclusion::Group {
                range: start..committed_position(committed),
                items,
            });
        }
    }
}

#[derive(Clone)]
struct AliasPrefix<'source> {
    leading: TriviaRun,
    keyword: WordSpan<'source>,
    after_keyword: Option<TriviaRun>,
    name: Option<WordSpan<'source>>,
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
    after_keyword: Option<TriviaRun>,
}

#[derive(Clone)]
struct WithoutPrefix<'source> {
    leading: TriviaRun,
    keyword: WordSpan<'source>,
    after_keyword: Option<TriviaRun>,
}

fn commit_maybe_use_alias<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<AliasPrefix<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let Some(leading) = scan_required_inline_trivia(i) else {
            i.rollback(checkpoint);
            return None;
        };
        let Some(keyword) = i.run(scan_word) else {
            i.rollback(checkpoint);
            return None;
        };
        if keyword.text() != "as" {
            i.rollback(checkpoint);
            return None;
        }
        let after_keyword = scan_maybe_required_inline_trivia(i);
        let name = after_keyword.as_ref().and_then(|_| i.run(scan_word));
        Some(AliasPrefix {
            leading,
            keyword,
            after_keyword,
            name,
        })
    })
}

fn commit_maybe_version<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<VersionPrefix<'source>>
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
        result
    })
}

fn commit_maybe_with_prefix<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<WithPrefix<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let Some(leading) = scan_required_inline_trivia(i) else {
            i.rollback(checkpoint);
            return None;
        };
        let Some(keyword) = i.run(scan_word) else {
            i.rollback(checkpoint);
            return None;
        };
        if keyword.text() != "with" {
            i.rollback(checkpoint);
            return None;
        }
        let after_keyword = scan_maybe_required_inline_trivia(i);
        Some(WithPrefix {
            leading,
            keyword,
            after_keyword,
        })
    })
}

fn commit_maybe_without_prefix<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<WithoutPrefix<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let Some(leading) = scan_required_inline_trivia(i) else {
            i.rollback(checkpoint);
            return None;
        };
        let Some(keyword) = i.run(scan_word) else {
            i.rollback(checkpoint);
            return None;
        };
        if keyword.text() != "without" {
            i.rollback(checkpoint);
            return None;
        }
        let after_keyword = scan_maybe_required_inline_trivia(i);
        Some(WithoutPrefix {
            leading,
            keyword,
            after_keyword,
        })
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

fn committed_at_eof<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| probe.input().input.remainder().is_empty())
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

/// A sink-free test for the first `UseTree` atom.  It intentionally does not
/// scan the whole tree: this is only the local-candidate decision used by the
/// declaration-head recovery rule.
fn commit_use_tree_candidate<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let candidate = i.input.remainder().starts_with('{')
            || i.input.remainder().starts_with('(')
            || i.run(scan_word).is_some()
            || i.run(parse_parenthesized_use_operator).is_some();
        i.rollback(checkpoint);
        candidate
    })
}

fn commit_parenthesized_use_operator_candidate<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| {
        probe
            .input()
            .input
            .remainder()
            .chars()
            .next()
            .is_some_and(is_use_operator_character)
    })
}

fn commit_use_exclusion_candidate<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        matches!(i.input.remainder().chars().next(), Some('(' | '{' | '*'))
            || i.run(scan_word).is_some()
    })
}

/// Consumes one contiguous invalid use-tree head episode, then leaves a later
/// locally-recognizable tree atom for the same slot to retry.  Statement and
/// group boundaries remain untouched for their owners.
fn use_tree_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let i = probe.input();
            let Some(character) = i.input.remainder().chars().next() else {
                return (start < end).then_some((start..end, false));
            };
            if matches!(character, '\r' | '\n' | ';' | ',' | '}' | ')') {
                return (start < end).then_some((start..end, false));
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            let candidate = i.input.remainder().starts_with('{')
                || i.input
                    .remainder()
                    .chars()
                    .next()
                    .is_some_and(|next| next == '_' || next.is_alphabetic());
            if candidate {
                return Some((start..end, true));
            }
        }
    });
    let Some((range, retry)) = recovered else {
        return false;
    };
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Import(ImportRole::Path));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Path,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
    retry
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
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let trivia = scan_required_inline_trivia(i);
        if trivia.is_none() {
            i.rollback(checkpoint);
        }
        trivia
    })
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
        let result = i
            .run(scan_punctuation)
            .and_then(|punctuation| match punctuation.kind() {
                PunctuationKind::ColonColon => {
                    Some((UseSeparator::ColonColon, punctuation.range()))
                }
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

/// A visibility-prefixed binding declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BindingDeclaration<'source> {
    visibility: Visibility,
    target: Recovered<Pattern<'source>>,
    definition: Option<BindingDefinition<'source>>,
    range: Range<usize>,
}

impl<'source> BindingDeclaration<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn visibility(&self) -> Visibility {
        self.visibility
    }

    pub(crate) fn target(&self) -> &Recovered<Pattern<'source>> {
        &self.target
    }

    pub(crate) fn definition(&self) -> Option<&BindingDefinition<'source>> {
        self.definition.as_ref()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BindingDefinition<'source> {
    equals: Range<usize>,
    body: Recovered<BindingBody<'source>>,
    range: Range<usize>,
}

impl<'source> BindingDefinition<'source> {
    pub(crate) fn equals(&self) -> Range<usize> { self.equals.clone() }
    pub(crate) fn body(&self) -> &Recovered<BindingBody<'source>> { &self.body }
    pub(crate) fn range(&self) -> Range<usize> { self.range.clone() }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum BindingBody<'source> {
    Inline { expression: OperatorChain<'source> },
    Indented { block: IndentedStatementBlock<'source> },
}

/// A module declaration has the same child shape at root and in a canonical
/// statement sequence; only its caller supplies a different wrapper.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ModDeclaration<'source> {
    visibility: Visibility,
    test_marker: Option<WordSpan<'source>>,
    name: Option<Recovered<WordSpan<'source>>>,
    body: Recovered<ModBody<'source>>,
    range: Range<usize>,
}

impl<'source> ModDeclaration<'source> {
    pub(crate) fn range(&self) -> Range<usize> { self.range.clone() }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ModBody<'source> {
    Bodyless { semicolon: Range<usize> },
    Braced { block: BracedStatementBlockExpression<'source> },
    Colon { colon: Recovered<Range<usize>>, body: Recovered<ModColonBody<'source>> },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ModColonBody<'source> {
    Inline { statement: Box<Statement<'source>> },
    Indented { block: IndentedStatementBlock<'source> },
}

/// A structure declaration shared by root and nested canonical Statements.
///
/// Its parser and direct-CST continuation are wired in later slices; these
/// types preserve the approved surface shape without introducing any future
/// declaration features.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StructDeclaration<'source> {
    visibility: Visibility,
    name: Recovered<WordSpan<'source>>,
    body: Recovered<StructBody<'source>>,
    range: Range<usize>,
}

impl StructDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

/// A parser-side equality declaration.  Its equality RHS remains syntax-only:
/// alias, nominal, and opaque semantics belong to later HIR ownership.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypeDeclaration<'source> {
    visibility: Visibility,
    name: Recovered<WordSpan<'source>>,
    parameters: Vec<DeclarationTypeParameter<'source>>,
    equals: Recovered<Range<usize>>,
    rhs: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
}

impl TypeDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DeclarationTypeParameter<'source> {
    Identifier(WordSpan<'source>),
    SigilIdentifier(WordSpan<'source>),
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum StructBody<'source> {
    Bodyless { semicolon: Range<usize> },
    NamedBraced(StructNamedBracedBody<'source>),
    NamedIndented(StructNamedIndentedBody<'source>),
    Tuple(StructTupleBody<'source>),
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StructNamedBracedBody<'source> {
    open: Range<usize>,
    fields: Vec<Recovered<StructNamedField<'source>>>,
    trailing_comma: Option<Range<usize>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StructNamedIndentedBody<'source> {
    colon: Range<usize>,
    base_indent: usize,
    block_indent: usize,
    fields: Vec<Recovered<StructNamedField<'source>>>,
    trailing_comma: Option<Range<usize>>,
    range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StructTupleBody<'source> {
    open: Range<usize>,
    fields: Vec<Recovered<StructTupleField<'source>>>,
    trailing_comma: Option<Range<usize>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StructNamedField<'source> {
    name: Recovered<WordSpan<'source>>,
    colon: Recovered<Range<usize>>,
    type_expr: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StructTupleField<'source> {
    type_expr: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
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
        parse_struct_declaration.map(Declaration::Struct),
        parse_type_declaration.map(Declaration::Type),
        parse_use_declaration.map(Declaration::Use),
        parse_operator_header.map(Declaration::OperatorHeader),
        parse_binding_declaration.map(Declaration::Binding),
        from_fn(|i| parse_mod_declaration_with_operators(&crate::operator::OperatorTable::empty(), i)).map(Declaration::Mod),
    ))
}

/// Parses the committed Struct header and its body introducer. Field sequences
/// remain deliberately unparsed until their dedicated declaration drivers
/// land, but a recognized introducer fixes the body family immediately.
pub(crate) fn parse_struct_declaration<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<StructDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let intro = i.run(recognize_struct_statement_intro)?;
    let _ = struct_continuation_trivia(intro.struct_base, &mut i);
    let mut name_incomplete = false;
    let name = if let Some(name) = i.run(scan_word) {
        Recovered::Complete(name)
    } else {
        match struct_name_error_retry_ast(&mut i) {
            Some(true) => Recovered::Complete(
                i.run(scan_word)
                    .expect("a Struct name retry must leave its raw word at the cursor"),
            ),
            Some(false) => {
                name_incomplete = true;
                Recovered::Incomplete
            }
            None => {
                name_incomplete = true;
                Recovered::Incomplete
            }
        }
    };
    let body_starter_pending = struct_body_starter_pending(&mut i);
    let body = if !name_incomplete || body_starter_pending {
        let _ = struct_continuation_trivia(intro.struct_base, &mut i);
        parse_struct_body_ast(intro.struct_base, &mut i).map_or(Recovered::Incomplete, Recovered::Complete)
    } else {
        Recovered::Incomplete
    };
    let end = match &body {
        Recovered::Complete(StructBody::Bodyless { semicolon }) => semicolon.end,
        Recovered::Complete(StructBody::NamedBraced(body)) => body.range.end,
        Recovered::Complete(StructBody::NamedIndented(body)) => body.range.end,
        Recovered::Complete(StructBody::Tuple(body)) => body.range.end,
        Recovered::Incomplete => match &name {
            Recovered::Complete(name) => name.range().end,
            Recovered::Incomplete => intro.struct_keyword.range().end,
        },
    };
    Some(StructDeclaration {
        visibility: intro.visibility.map_or(Visibility::Private, |prefix| prefix.visibility),
        name,
        body,
        range: intro.start..end,
    })
}

fn parse_struct_body_ast<'source, E>(
    struct_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<StructBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut starter = struct_body_starter(i);
    if starter.is_none() && !struct_word_pending(i) {
        if struct_body_introducer_error_retry_ast(i).is_some_and(|retry| retry) {
            starter = struct_body_starter(i);
        }
    }
    let starter = starter?;
    let punctuation = i.run(scan_punctuation).expect("a selected Struct body starter remains available");
    match starter {
        StructBodyStarter::Bodyless(range) => {
            debug_assert_eq!(punctuation.range(), range);
            Some(StructBody::Bodyless { semicolon: range })
        }
        StructBodyStarter::NamedBraced(range) => {
            debug_assert_eq!(punctuation.range(), range);
            Some(StructBody::NamedBraced(parse_struct_named_braced_body_ast(struct_base, range, i)))
        }
        StructBodyStarter::Tuple(range) => {
            debug_assert_eq!(punctuation.range(), range);
            Some(StructBody::Tuple(parse_struct_tuple_body_ast(struct_base, range, i)))
        }
        StructBodyStarter::NamedIndented(range) => {
            debug_assert_eq!(punctuation.range(), range);
            Some(StructBody::NamedIndented(
                parse_struct_named_indented_body_ast(struct_base, range, i),
            ))
        }
    }
}

fn parse_struct_named_indented_body_ast<'source, E>(
    struct_base: usize,
    colon: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> StructNamedIndentedBody<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let Some((opening, block_indent)) = consume_struct_indented_opening(struct_base, i) else {
        return StructNamedIndentedBody {
            colon: colon.clone(),
            base_indent: struct_base,
            block_indent: struct_base,
            fields: vec![Recovered::Incomplete],
            trailing_comma: None,
            range: colon,
        };
    };
    let stops = i.local.stop_set().unwrap_or_default()
        .without(StopKind::Newline)
        .with(StopKind::Comma);
    i.local.push_stop_set(stops);
    push_struct_indented_layout(block_indent, i);

    let mut fields = Vec::new();
    let mut trailing_comma = None;
    loop {
        if struct_indented_terminal_boundary_pending(block_indent, i) {
            if fields.is_empty() {
                fields.push(Recovered::Incomplete);
            }
            break;
        }
        if let Some(comma) = scan_struct_comma(i) {
            fields.push(Recovered::Incomplete);
            match consume_struct_indented_gap(block_indent, i) {
                StructIndentedGap::Dedent => {
                    trailing_comma = Some(comma);
                    break;
                }
                StructIndentedGap::Trivia(_) if struct_indented_terminal_boundary_pending(block_indent, i) => {
                    trailing_comma = Some(comma);
                    break;
                }
                StructIndentedGap::Trivia(_) => continue,
            }
        }
        if scan_struct_semicolon(i).is_some() {
            match consume_struct_indented_gap(block_indent, i) {
                StructIndentedGap::Dedent => break,
                StructIndentedGap::Trivia(_) => continue,
            }
        }

        let field = if let Some(field) = parse_struct_named_field_ast(false, i) {
            Recovered::Complete(field)
        } else if scan_struct_field_invalid_run(false, i).is_some() {
            Recovered::Incomplete
        } else {
            fields.push(Recovered::Incomplete);
            break;
        };
        fields.push(field);

        let gap = consume_struct_indented_gap(block_indent, i);
        if matches!(gap, StructIndentedGap::Dedent) {
            break;
        }
        let StructIndentedGap::Trivia(trivia) = gap else { unreachable!() };
        if struct_trivia_has_newline(&trivia) && i.local.line().line_indent == block_indent {
            continue;
        }
        if let Some(comma) = scan_struct_comma(i) {
            let post = consume_struct_indented_gap(block_indent, i);
            match post {
                StructIndentedGap::Dedent => {
                    trailing_comma = Some(comma);
                    break;
                }
                StructIndentedGap::Trivia(_) if struct_indented_terminal_boundary_pending(block_indent, i) => {
                    trailing_comma = Some(comma);
                    break;
                }
                StructIndentedGap::Trivia(_) => continue,
            }
        }
        if scan_struct_semicolon(i).is_some() {
            match consume_struct_indented_gap(block_indent, i) {
                StructIndentedGap::Dedent => break,
                StructIndentedGap::Trivia(_) => continue,
            }
        }
        if struct_indented_terminal_boundary_pending(block_indent, i) {
            break;
        }
        if struct_next_named_field_candidate(i, &trivia) {
            continue;
        }
        break;
    }

    pop_struct_indented_layout(block_indent, i);
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    let end = i.pos();
    let _ = opening;
    StructNamedIndentedBody {
        colon: colon.clone(),
        base_indent: struct_base,
        block_indent,
        fields,
        trailing_comma,
        range: colon.start..end,
    }
}

/// Parse the parenthesis-owned tuple field sequence.  It shares the Struct
/// list frame with named braces, but a tuple field is its mandatory type slot
/// directly: there is no field-head authority or named-field TypeApply guard.
fn parse_struct_tuple_body_ast<'source, E>(
    struct_base: usize,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> StructTupleBody<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let stops = i.local.stop_set().unwrap_or_default()
        .without(StopKind::Newline)
        .with(StopKind::Comma)
        .with(StopKind::RightParenthesis);
    i.local.push_delimiter(Delimiter::Parenthesis);
    i.local.push_stop_set(stops);
    let opening = i.run(scan_trivia).expect("trivia is total");
    let layout = LayoutDelimitedFrame::after_opening_trivia(
        struct_base,
        &opening,
        i.local.line().line_indent,
    );
    push_struct_layout(layout, i);

    let mut fields = Vec::new();
    let mut trailing_comma = None;
    let close = loop {
        if let Some(close) = scan_struct_close_parenthesis(i) {
            break Recovered::Complete(close);
        }
        if struct_outer_owned_mismatched_close_pending_for(Delimiter::Parenthesis, i) {
            break Recovered::Incomplete;
        }
        if scan_struct_mismatched_close_for(Delimiter::Parenthesis, i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        if i.input.remainder().is_empty() {
            break Recovered::Incomplete;
        }
        if scan_struct_comma(i).is_some() {
            fields.push(Recovered::Incomplete);
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        if scan_struct_semicolon(i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }

        let type_expr = i.run(from_fn(|i| Some(
            parse_required_type_expression_with_outer_missing_role(
                Some(GrammarRole::Declaration(DeclarationRole::Struct(
                    crate::session::StructRole::FieldType,
                ))),
                i,
            )
        ))).expect("mandatory type expression is total");
        match type_expr {
            Recovered::Complete(type_expr) => fields.push(Recovered::Complete(StructTupleField {
                range: type_expr.range(),
                type_expr: Recovered::Complete(Box::new(type_expr)),
            })),
            Recovered::Incomplete => fields.push(Recovered::Incomplete),
        }

        if any_ambient_owner_claims(i) {
            break Recovered::Incomplete;
        }

        let trivia = i.run(scan_trivia).expect("trivia is total");
        if let Some(comma) = scan_struct_comma(i) {
            let post = i.run(scan_trivia).expect("trivia is total");
            if let Some(close) = scan_struct_close_parenthesis(i) {
                trailing_comma = Some(comma);
                break Recovered::Complete(close);
            }
            if i.input.remainder().is_empty()
                || struct_outer_owned_mismatched_close_pending_for(Delimiter::Parenthesis, i)
            {
                fields.push(Recovered::Incomplete);
                break Recovered::Incomplete;
            }
            let _ = post;
            continue;
        }
        if let Some(close) = scan_struct_close_parenthesis(i) {
            break Recovered::Complete(close);
        }
        if layout.boundary_after_trivia(&trivia, i.local.line().line_indent)
            == LayoutDelimitedBoundary::ImplicitNewline
        {
            continue;
        }
        if struct_outer_owned_mismatched_close_pending_for(Delimiter::Parenthesis, i) {
            break Recovered::Incomplete;
        }
        if scan_struct_mismatched_close_for(Delimiter::Parenthesis, i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        if scan_struct_semicolon(i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        break Recovered::Incomplete;
    };

    pop_struct_layout(layout, i);
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    let end = match &close {
        Recovered::Complete(close) => close.end,
        Recovered::Incomplete => i.pos(),
    };
    StructTupleBody { open: open.clone(), fields, trailing_comma, close, range: open.start..end }
}

/// Parse the brace-owned named field sequence.  The layout frame is captured
/// once after the opener; unlike type records, this declaration owns its own
/// field and close recovery vocabulary.
fn parse_struct_named_braced_body_ast<'source, E>(
    struct_base: usize,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> StructNamedBracedBody<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let incoming = struct_base;
    let stops = i.local.stop_set().unwrap_or_default()
        .without(StopKind::Newline)
        .with(StopKind::Comma)
        .with(StopKind::RightBrace);
    i.local.push_delimiter(Delimiter::Brace);
    i.local.push_stop_set(stops);
    let opening = i.run(scan_trivia).expect("trivia is total");
    let layout = LayoutDelimitedFrame::after_opening_trivia(
        incoming,
        &opening,
        i.local.line().line_indent,
    );
    push_struct_layout(layout, i);

    let mut fields = Vec::new();
    let mut trailing_comma = None;
    let close = loop {
        if let Some(close) = scan_struct_close_brace(i) {
            break Recovered::Complete(close);
        }
        if struct_outer_owned_mismatched_close_pending(i) {
            break Recovered::Incomplete;
        }
        if scan_struct_mismatched_close(i).is_some() {
            // A local mismatched closer belongs to this close slot.  Its
            // following trivia must not manufacture an empty field before
            // the retry reaches this frame's matching close.
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        if i.input.remainder().is_empty() {
            break Recovered::Incomplete;
        }
        if let Some(_comma) = scan_struct_comma(i) {
            fields.push(Recovered::Incomplete);
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        if scan_struct_semicolon(i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        let field = if let Some(field) = parse_struct_named_field_ast(true, i) {
            Recovered::Complete(field)
        } else if scan_struct_field_invalid_run(false, i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            Recovered::Incomplete
        } else {
            break Recovered::Incomplete;
        };
        fields.push(field);

        if matches!(fields.last(), Some(Recovered::Incomplete)) {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            continue;
        }

        if any_ambient_owner_claims(i) {
            break Recovered::Incomplete;
        }
        let trivia = i.run(scan_trivia).expect("trivia is total");
        if let Some(comma) = scan_struct_comma(i) {
            let post = i.run(scan_trivia).expect("trivia is total");
            if let Some(close) = scan_struct_close_brace(i) {
                trailing_comma = Some(comma);
                break Recovered::Complete(close);
            }
            if i.input.remainder().is_empty() || struct_outer_owned_mismatched_close_pending(i) {
                fields.push(Recovered::Incomplete);
                break Recovered::Incomplete;
            }
            let _ = post;
            continue;
        }
        if let Some(close) = scan_struct_close_brace(i) {
            break Recovered::Complete(close);
        }
        if layout.boundary_after_trivia(&trivia, i.local.line().line_indent)
            == LayoutDelimitedBoundary::ImplicitNewline
        {
            if i.input.remainder().is_empty() || struct_outer_owned_mismatched_close_pending(i) {
                fields.push(Recovered::Incomplete);
                break Recovered::Incomplete;
            }
            continue;
        }
        if struct_next_named_field_candidate(i, &trivia) {
            continue;
        }
        if struct_outer_owned_mismatched_close_pending(i) {
            break Recovered::Incomplete;
        }
        if scan_struct_mismatched_close(i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        if scan_struct_semicolon(i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        break Recovered::Incomplete;
    };

    pop_struct_layout(layout, i);
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Brace));
    let end = match &close {
        Recovered::Complete(close) => close.end,
        Recovered::Incomplete => i.pos(),
    };
    StructNamedBracedBody { open: open.clone(), fields, trailing_comma, close, range: open.start..end }
}

fn parse_struct_named_field_ast<'source, E>(
    ambient_sensitive: bool,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<StructNamedField<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let name_recovery = if struct_word_pending(i) || struct_colon_pending(i) {
        None
    } else {
        scan_struct_field_name_colon_recovery(i)
    };
    let name = if let Some(name) = i.run(scan_word) {
        Recovered::Complete(name)
    } else if struct_colon_pending(i) {
        Recovered::Incomplete
    } else if matches!(name_recovery, Some(StructFieldInvalidRun { target: StructFieldInvalidTarget::Colon { .. }, .. })) {
        Recovered::Incomplete
    } else {
        return None;
    };
    let name_end = match &name {
        Recovered::Complete(name) => name.range().end,
        Recovered::Incomplete => start,
    };
    let _ = consume_struct_field_name_trivia(i);
    let colon_recovery = if struct_colon_pending(i) || struct_field_boundary_pending(i) {
        None
    } else {
        scan_struct_field_invalid_run(true, i)
    };
    let colon = if let Some(colon) = scan_struct_colon(i) {
        Recovered::Complete(colon)
    } else {
        Recovered::Incomplete
    };
    let type_expr = if (ambient_sensitive && any_ambient_owner_claims(i))
        || matches!(colon_recovery, Some(StructFieldInvalidRun { target: StructFieldInvalidTarget::Boundary, .. }))
        || (matches!(colon, Recovered::Incomplete) && struct_field_boundary_pending(i))
    {
        Recovered::Incomplete
    } else {
        let _ = consume_struct_field_type_trivia(i);
        i.local.push_type_delimited_owner(TypeDelimitedOwner::StructNamedFields);
        let parsed = i.run(from_fn(|i| Some(
            parse_required_type_expression_with_outer_missing_role(
                Some(GrammarRole::Declaration(DeclarationRole::Struct(
                    crate::session::StructRole::FieldType,
                ))),
                i,
            )
        ))).expect("mandatory type expression is total");
        assert_eq!(
            i.local.pop_type_delimited_owner(),
            Some(TypeDelimitedOwner::StructNamedFields),
        );
        match parsed {
            Recovered::Complete(type_expr) => Recovered::Complete(Box::new(type_expr)),
            Recovered::Incomplete => Recovered::Incomplete,
        }
    };
    let end = match &type_expr {
        Recovered::Complete(type_expr) => type_expr.range().end,
        Recovered::Incomplete => match &colon {
            Recovered::Complete(colon) => colon.end,
            Recovered::Incomplete => name_end,
        },
    };
    Some(StructNamedField { name, colon, type_expr, range: start..end })
}

fn commit_struct_named_braced_body<'parse, 'source, 'local, E, O>(
    struct_base: usize,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let incoming = struct_base;
    let stops = committed.probe(|probe| {
        probe.input().local.stop_set().unwrap_or_default()
            .without(StopKind::Newline)
            .with(StopKind::Comma)
            .with(StopKind::RightBrace)
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_delimiter(Delimiter::Brace);
        i.local.push_stop_set(stops);
    });
    let opening = committed.probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia is total");
    committed.emit_trivia(&opening);
    let layout = committed.probe(|probe| {
        LayoutDelimitedFrame::after_opening_trivia(
            incoming,
            &opening,
            probe.input().local.line().line_indent,
        )
    });
    committed.probe(|probe| push_struct_layout(layout, probe.input()));

    loop {
        if let Some(close) = committed.probe(|probe| scan_struct_close_brace(probe.input())) {
            committed.token(SyntaxKind::RBrace, close);
            break;
        }
        if committed.probe(|probe| struct_outer_owned_mismatched_close_pending(probe.input())) {
            emit_struct_missing_close(committed);
            break;
        }
        if let Some((range, actual)) = committed.probe(|probe| scan_struct_mismatched_close(probe.input())) {
            emit_struct_mismatched_close(committed, range, actual);
            // Keep recovery at the close slot: trivia after a consumed local
            // mismatch precedes the next close retry, not a field slot.
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close(committed);
                break;
            }
            let trivia = committed.probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if committed.probe(|probe| probe.input().input.remainder().is_empty()) {
            emit_struct_missing_close(committed);
            break;
        }
        if committed.probe(|probe| scan_struct_comma_pending(probe.input())) {
            commit_empty_struct_named_field(committed);
            let comma = committed
                .probe(|probe| scan_struct_comma(probe.input()))
                .expect("the empty Struct field slot is followed by its comma");
            committed.token(SyntaxKind::Comma, comma);
            let trivia = committed.probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if let Some(semicolon) = committed.probe(|probe| scan_struct_semicolon(probe.input())) {
            emit_struct_error(
                committed,
                crate::session::StructRole::FieldSeparator,
                semicolon,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close(committed);
                break;
            }
            let trivia = committed.probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if !commit_struct_named_field(true, committed) {
            if let Some(run) = committed.probe(|probe| scan_struct_field_invalid_run(false, probe.input())) {
                emit_struct_error(
                    committed,
                    crate::session::StructRole::Field,
                    run.range,
                    ExpectedSyntax::Identifier,
                );
                if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                    emit_struct_missing_close(committed);
                    break;
                }
                let trivia = committed.probe(|probe| probe.input().run(scan_trivia))
                    .expect("trivia is total");
                committed.emit_trivia(&trivia);
                continue;
            } else {
                emit_struct_missing(committed, crate::session::StructRole::Field, ExpectedSyntax::Identifier);
                break;
            }
        }

        if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
            emit_struct_missing_close(committed);
            break;
        }
        let trivia = committed.probe(|probe| probe.input().run(scan_trivia))
            .expect("trivia is total");
        committed.emit_trivia(&trivia);
        if let Some(comma) = committed.probe(|probe| scan_struct_comma(probe.input())) {
            committed.token(SyntaxKind::Comma, comma);
            let post = committed.probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&post);
            if let Some(close) = committed.probe(|probe| scan_struct_close_brace(probe.input())) {
                committed.token(SyntaxKind::RBrace, close);
                break;
            }
            if committed.probe(|probe| {
                probe.input().input.remainder().is_empty()
                    || struct_outer_owned_mismatched_close_pending(probe.input())
            }) {
                emit_struct_missing(committed, crate::session::StructRole::Field, ExpectedSyntax::Identifier);
                emit_struct_missing_close(committed);
                break;
            }
            continue;
        }
        if let Some(close) = committed.probe(|probe| scan_struct_close_brace(probe.input())) {
            committed.token(SyntaxKind::RBrace, close);
            break;
        }
        if committed.probe(|probe| {
            layout.boundary_after_trivia(&trivia, probe.input().local.line().line_indent)
                == LayoutDelimitedBoundary::ImplicitNewline
        }) {
            if committed.probe(|probe| {
                probe.input().input.remainder().is_empty()
                    || struct_outer_owned_mismatched_close_pending(probe.input())
            }) {
                emit_struct_missing(committed, crate::session::StructRole::Field, ExpectedSyntax::Identifier);
                emit_struct_missing_close(committed);
                break;
            }
            continue;
        }
        if committed.probe(|probe| struct_next_named_field_candidate(probe.input(), &trivia)) {
            emit_struct_missing(
                committed,
                crate::session::StructRole::FieldSeparator,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            continue;
        }
        if committed.probe(|probe| struct_outer_owned_mismatched_close_pending(probe.input())) {
            emit_struct_missing_close(committed);
            break;
        }
        if let Some((range, actual)) = committed.probe(|probe| scan_struct_mismatched_close(probe.input())) {
            emit_struct_mismatched_close(committed, range, actual);
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close(committed);
                break;
            }
            let trivia = committed.probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if let Some(semicolon) = committed.probe(|probe| scan_struct_semicolon(probe.input())) {
            emit_struct_error(
                committed,
                crate::session::StructRole::FieldSeparator,
                semicolon,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close(committed);
                break;
            }
            let trivia = committed.probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        emit_struct_missing_close(committed);
        break;
    }

    committed.probe(|probe| {
        let i = probe.input();
        pop_struct_layout(layout, i);
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Brace));
    });
    let _ = open;
}

fn commit_empty_struct_named_field<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.start_node(SyntaxKind::StructField);
    emit_struct_missing(committed, crate::session::StructRole::Field, ExpectedSyntax::Identifier);
    committed.finish_node();
}

fn commit_struct_named_field<'parse, 'source, 'local, E, O>(
    ambient_sensitive: bool,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let name = commit_word(committed);
    let colon_without_name = if name.is_none() {
        committed.probe(|probe| scan_struct_colon(probe.input()))
    } else {
        None
    };
    let malformed_name = if name.is_none() && colon_without_name.is_none() {
        committed.probe(|probe| scan_struct_field_name_colon_recovery(probe.input()))
    } else {
        None
    };
    if name.is_none() && colon_without_name.is_none() && malformed_name.is_none() {
        return false;
    }
    committed.start_node(SyntaxKind::StructField);
    if let Some(name) = name {
        committed.token(SyntaxKind::Identifier, name.range());
        if let Some(trivia) = committed.probe(|probe| consume_struct_field_name_trivia(probe.input())) {
            committed.emit_trivia(&trivia);
        }
    } else {
        match malformed_name {
            Some(StructFieldInvalidRun {
                range,
                target: StructFieldInvalidTarget::Colon { trivia },
            }) => {
                emit_struct_error(
                    committed,
                    crate::session::StructRole::FieldName,
                    range,
                    ExpectedSyntax::Identifier,
                );
                if let Some(trivia) = trivia {
                    committed.emit_trivia(&trivia);
                }
            }
            _ => emit_struct_missing(committed, crate::session::StructRole::FieldName, ExpectedSyntax::Identifier),
        }
    }
    let colon = colon_without_name.or_else(|| committed.probe(|probe| scan_struct_colon(probe.input())));
    if let Some(colon) = colon {
        committed.token(SyntaxKind::Colon, colon);
    } else {
        let recovery = if committed.probe(|probe| struct_field_boundary_pending(probe.input())) {
            None
        } else {
            committed.probe(|probe| scan_struct_field_invalid_run(true, probe.input()))
        };
        let type_expected = match recovery {
            Some(StructFieldInvalidRun { range, target }) => {
                emit_struct_error(
                    committed,
                    crate::session::StructRole::FieldColon,
                    range,
                    ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
                );
                match target {
                    StructFieldInvalidTarget::Colon { trivia } => {
                        if let Some(trivia) = trivia {
                            committed.emit_trivia(&trivia);
                        }
                        let colon = committed
                            .probe(|probe| scan_struct_colon(probe.input()))
                            .expect("field-colon recovery stopped at a colon");
                        committed.token(SyntaxKind::Colon, colon);
                        true
                    }
                    StructFieldInvalidTarget::TypePrimary { trivia } => {
                        if let Some(trivia) = trivia {
                            committed.emit_trivia(&trivia);
                        }
                        true
                    }
                    StructFieldInvalidTarget::Boundary => false,
                }
            }
            None => {
                emit_struct_missing(
                    committed,
                    crate::session::StructRole::FieldColon,
                    ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
                );
                !committed.probe(|probe| struct_field_boundary_pending(probe.input()))
            }
        };
        if !type_expected {
            committed.finish_node();
            return true;
        }
    }
    if ambient_sensitive && committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        emit_struct_missing(
            committed,
            crate::session::StructRole::FieldType,
            ExpectedSyntax::TypeExpression,
        );
        committed.finish_node();
        return true;
    }
    if let Some(trivia) = committed.probe(|probe| consume_struct_field_type_trivia(probe.input())) {
        committed.emit_trivia(&trivia);
    }
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_type_delimited_owner(TypeDelimitedOwner::StructNamedFields);
    });
    let _ = commit_direct_type_expression_with_outer_missing_role(
        Some(GrammarRole::Declaration(DeclarationRole::Struct(
            crate::session::StructRole::FieldType,
        ))),
        committed,
    );
    committed.probe(|probe| {
        assert_eq!(
            probe.input().local.pop_type_delimited_owner(),
            Some(TypeDelimitedOwner::StructNamedFields),
        );
    });
    committed.finish_node();
    true
}

fn push_struct_layout<E>(layout: LayoutDelimitedFrame, i: &mut SynIn<E>)
where E: ErrorSink<usize> {
    i.local.push_indentation_baseline(IndentationBaseline {
        column: layout.base_indent(),
        kind: IndentationBaselineKind::Introducer,
    });
}

fn pop_struct_layout<E>(layout: LayoutDelimitedFrame, i: &mut SynIn<E>)
where E: ErrorSink<usize> {
    assert_eq!(
        i.local.pop_indentation_baseline(),
        Some(IndentationBaseline { column: layout.base_indent(), kind: IndentationBaselineKind::Introducer }),
    );
}

fn push_struct_indented_layout<E>(block_indent: usize, i: &mut SynIn<E>)
where E: ErrorSink<usize> {
    i.local.push_indentation_baseline(IndentationBaseline {
        column: block_indent,
        kind: IndentationBaselineKind::Block,
    });
}

fn pop_struct_indented_layout<E>(block_indent: usize, i: &mut SynIn<E>)
where E: ErrorSink<usize> {
    assert_eq!(
        i.local.pop_indentation_baseline(),
        Some(IndentationBaseline {
            column: block_indent,
            kind: IndentationBaselineKind::Block,
        })
    );
}

#[derive(Clone, Debug)]
enum StructIndentedGap {
    Trivia(TriviaRun),
    Dedent,
}

/// The colon body owns its opening run only when the first field line is
/// strictly deeper than the Struct header. Other trivia remains caller-owned
/// while its mandatory first field slot is recovered.
fn consume_struct_indented_opening<E>(
    struct_base: usize,
    i: &mut SynIn<E>,
) -> Option<(TriviaRun, usize)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia is total");
    let block_indent = i.local.line().line_indent;
    if struct_trivia_has_newline(&trivia) && block_indent > struct_base {
        Some((trivia, block_indent))
    } else {
        i.rollback(checkpoint);
        None
    }
}

/// Consume one inter-field gap without stealing a dedent. A same-column
/// newline is the implicit separator; a deeper line stays ordinary trivia so
/// the mandatory type entry retains continuation authority.
fn consume_struct_indented_gap<E>(
    block_indent: usize,
    i: &mut SynIn<E>,
) -> StructIndentedGap
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia is total");
    if struct_trivia_has_newline(&trivia) && i.local.line().line_indent < block_indent {
        i.rollback(checkpoint);
        StructIndentedGap::Dedent
    } else {
        StructIndentedGap::Trivia(trivia)
    }
}

fn commit_struct_indented_gap<'parse, 'source, 'local, E, O>(
    block_indent: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> StructIndentedGap
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let gap = committed.probe(|probe| consume_struct_indented_gap(block_indent, probe.input()));
    if let StructIndentedGap::Trivia(trivia) = &gap {
        committed.emit_trivia(trivia);
    }
    gap
}

fn struct_indented_terminal_boundary_pending<E>(
    block_indent: usize,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty() || struct_outer_close_pending(i) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let gap = consume_struct_indented_gap(block_indent, i);
    let terminal = matches!(gap, StructIndentedGap::Dedent);
    i.rollback(checkpoint);
    terminal
}

fn struct_outer_close_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        let stop = match punctuation.kind() {
            PunctuationKind::Close(Delimiter::Parenthesis) => Some(StopKind::RightParenthesis),
            PunctuationKind::Close(Delimiter::Bracket) => Some(StopKind::RightBracket),
            PunctuationKind::Close(Delimiter::Brace) => Some(StopKind::RightBrace),
            _ => None,
        };
        stop.is_some_and(|stop| i.local.stop_set().is_some_and(|stops| stops.contains(stop)))
    });
    i.rollback(checkpoint);
    pending
}

fn consume_struct_field_name_trivia<E>(i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia is total");
    if struct_trivia_has_newline(&trivia) {
        i.rollback(checkpoint);
        None
    } else {
        Some(trivia)
    }
}

fn consume_struct_field_type_trivia<E>(i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia is total");
    let base = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
    if struct_trivia_has_newline(&trivia) && i.local.line().line_indent <= base {
        i.rollback(checkpoint);
        None
    } else {
        Some(trivia)
    }
}

fn struct_next_named_field_candidate<E>(i: &mut SynIn<E>, leading: &TriviaRun) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if leading.is_empty() || struct_trivia_has_newline(leading) {
        return false;
    }
    let checkpoint = i.checkpoint();
    let candidate = i.run(scan_word).is_some_and(|_| {
        let gap = i.run(scan_trivia).expect("trivia is total");
        !struct_trivia_has_newline(&gap) && scan_struct_colon(i).is_some()
    });
    i.rollback(checkpoint);
    candidate
}

#[derive(Clone, Debug)]
struct StructFieldInvalidRun {
    range: Range<usize>,
    target: StructFieldInvalidTarget,
}

#[derive(Clone, Debug)]
enum StructFieldInvalidTarget {
    Colon { trivia: Option<TriviaRun> },
    TypePrimary { trivia: Option<TriviaRun> },
    Boundary,
}

/// Scan one declaration-owned malformed field slot.  It is intentionally
/// narrower than header recovery: a field name can recover only to a colon
/// skeleton, while a field colon may also hand the same slot to a TypePrimary.
fn scan_struct_field_invalid_run<E>(
    allow_type_primary: bool,
    i: &mut SynIn<E>,
) -> Option<StructFieldInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let mut end = start;
    loop {
        if end == start && (struct_colon_pending(i) || (allow_type_primary && struct_type_primary_pending(i))) {
            return None;
        }
        if end > start {
            if struct_colon_pending(i) {
                return Some(StructFieldInvalidRun {
                    range: start..end,
                    target: StructFieldInvalidTarget::Colon { trivia: None },
                });
            }
            if allow_type_primary && struct_type_primary_pending(i) {
                return Some(StructFieldInvalidRun {
                    range: start..end,
                    target: StructFieldInvalidTarget::TypePrimary { trivia: None },
                });
            }
            if !allow_type_primary && struct_raw_field_head_pending(i) {
                return Some(StructFieldInvalidRun {
                    range: start..end,
                    target: StructFieldInvalidTarget::Boundary,
                });
            }

            let checkpoint = i.checkpoint();
            let trivia = i.run(scan_trivia).expect("trivia is total");
            if !trivia.is_empty() {
                if struct_trivia_has_newline(&trivia) {
                    i.rollback(checkpoint);
                    return Some(StructFieldInvalidRun { range: start..end, target: StructFieldInvalidTarget::Boundary });
                }
                if struct_colon_pending(i) {
                    return Some(StructFieldInvalidRun {
                        range: start..end,
                        target: StructFieldInvalidTarget::Colon { trivia: Some(trivia) },
                    });
                }
                if allow_type_primary && struct_type_primary_pending(i) {
                    return Some(StructFieldInvalidRun {
                        range: start..end,
                        target: StructFieldInvalidTarget::TypePrimary { trivia: Some(trivia) },
                    });
                }
                i.rollback(checkpoint);
                return Some(StructFieldInvalidRun {
                    range: start..end,
                    target: StructFieldInvalidTarget::Boundary,
                });
            }
            if struct_field_boundary_pending(i) || struct_mismatched_close_pending(i) {
                return Some(StructFieldInvalidRun { range: start..end, target: StructFieldInvalidTarget::Boundary });
            }
        }

        if let Some(colon_colon) = scan_struct_colon_colon(i) {
            end = colon_colon.end;
            continue;
        }
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n') {
            return (start < end).then_some(StructFieldInvalidRun {
                range: start..end,
                target: StructFieldInvalidTarget::Boundary,
            });
        }
        i.input.next()?;
        end = i.pos();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

/// A malformed field name establishes field authority only if it reaches the
/// literal-colon skeleton.  Other malformed input remains sequence-owned.
fn scan_struct_field_name_colon_recovery<E>(
    i: &mut SynIn<E>,
) -> Option<StructFieldInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let recovered = scan_struct_field_invalid_run(false, i);
    if matches!(recovered, Some(StructFieldInvalidRun { target: StructFieldInvalidTarget::Colon { .. }, .. })) {
        recovered
    } else {
        i.rollback(checkpoint);
        None
    }
}

fn struct_type_primary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(parse_type_expression).is_some();
    i.rollback(checkpoint);
    pending
}

fn struct_raw_field_head_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_word).is_some();
    i.rollback(checkpoint);
    pending
}

fn struct_field_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.input.remainder().is_empty()
        || scan_struct_comma_pending(i)
        || struct_close_brace_pending(i)
        || struct_semicolon_pending(i)
        || struct_mismatched_close_pending(i)
        || struct_field_newline_boundary_pending(i)
}

fn struct_field_newline_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia is total");
    let pending = struct_trivia_has_newline(&trivia);
    i.rollback(checkpoint);
    pending
}

fn scan_struct_comma_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_struct_comma(i).is_some();
    i.rollback(checkpoint);
    pending
}

fn struct_colon_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_struct_colon(i).is_some();
    i.rollback(checkpoint);
    pending
}

fn struct_close_brace_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_struct_close_brace(i).is_some();
    i.rollback(checkpoint);
    pending
}

fn struct_mismatched_close_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(punctuation.kind(), PunctuationKind::Close(delimiter) if delimiter != Delimiter::Brace)
    });
    i.rollback(checkpoint);
    pending
}

fn scan_struct_mismatched_close<E>(i: &mut SynIn<E>) -> Option<(Range<usize>, Delimiter)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_mismatched_close_for(Delimiter::Brace, i)
}

fn scan_struct_mismatched_close_for<E>(
    expected: Delimiter,
    i: &mut SynIn<E>,
) -> Option<(Range<usize>, Delimiter)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    match punctuation.kind() {
        PunctuationKind::Close(delimiter) if delimiter != expected => {
            Some((punctuation.range(), delimiter))
        }
        _ => {
            i.rollback(checkpoint);
            None
        }
    }
}

/// Each Struct field frame keeps incoming stops beneath its own matching
/// delimiter. A mismatched closer is outer-owned exactly when its corresponding
/// incoming stop remains active; it must remain untouched for that owner.
fn struct_outer_owned_mismatched_close_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    struct_outer_owned_mismatched_close_pending_for(Delimiter::Brace, i)
}

fn struct_outer_owned_mismatched_close_pending_for<E>(
    expected: Delimiter,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_struct_mismatched_close_for(expected, i).is_some_and(|(_, delimiter)| {
        let stop = match delimiter {
            Delimiter::Parenthesis => StopKind::RightParenthesis,
            Delimiter::Bracket => StopKind::RightBracket,
            Delimiter::Brace => StopKind::RightBrace,
        };
        i.local.stop_set().is_some_and(|stops| stops.contains(stop))
    });
    i.rollback(checkpoint);
    pending
}

fn scan_struct_comma<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_punctuation(PunctuationKind::Comma, i)
}

fn scan_struct_colon<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_punctuation(PunctuationKind::Colon, i)
}

fn scan_struct_close_brace<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_close(Delimiter::Brace, i)
}

fn scan_struct_close_parenthesis<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_close(Delimiter::Parenthesis, i)
}

fn scan_struct_close<E>(delimiter: Delimiter, i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_punctuation(PunctuationKind::Close(delimiter), i)
}

fn scan_struct_semicolon<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_punctuation(PunctuationKind::Semicolon, i)
}

fn struct_semicolon_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_struct_semicolon(i).is_some();
    i.rollback(checkpoint);
    pending
}

fn scan_struct_colon_colon<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_punctuation(PunctuationKind::ColonColon, i)
}

fn scan_struct_punctuation<E>(kind: PunctuationKind, i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    if punctuation.kind() == kind {
        Some(punctuation.range())
    } else {
        i.rollback(checkpoint);
        None
    }
}

fn struct_trivia_has_newline(trivia: &TriviaRun) -> bool {
    trivia.parts().iter().any(|part| matches!(part.kind(), TriviaPartKind::Newline))
}

fn emit_struct_missing_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_struct_missing_close_for(committed, ConstructRole::StructNamedFields, Delimiter::Brace);
}

fn emit_struct_missing_close_for<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    owner: ConstructRole,
    delimiter: Delimiter,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::ClosingDelimiter {
            owner,
            delimiter,
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role, range: at..at },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(delimiter)),
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_struct_mismatched_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
    actual: Delimiter,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_struct_mismatched_close_for(
        committed,
        ConstructRole::StructNamedFields,
        Delimiter::Brace,
        range,
        actual,
    );
}

fn emit_struct_mismatched_close_for<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    owner: ConstructRole,
    delimiter: Delimiter,
    range: Range<usize>,
    actual: Delimiter,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::ClosingDelimiter {
            owner,
            delimiter,
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role, range: range.clone() },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::Punctuation(
                    crate::session::PunctuationEvidence::Close(actual),
                ),
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(delimiter)),
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn emit_struct_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: crate::session::StructRole,
    range: Range<usize>,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Struct(role));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role, range: range.clone() },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected,
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn struct_name_error_retry_ast<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    struct_error_retry_ast(
        i,
        |i| struct_body_starter_pending(i),
        |i| struct_word_pending(i),
        |_| false,
    )
}

fn struct_body_introducer_error_retry_ast<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    struct_error_retry_ast(
        i,
        |_| false,
        |i| struct_body_starter_pending(i),
        |i| struct_word_pending(i) || struct_double_colon_pending(i),
    )
}

fn struct_error_retry_ast<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
    safe_boundary: impl Fn(&mut SynIn<'_, 'source, '_, E>) -> bool,
    retry_after_error: impl Fn(&mut SynIn<'_, 'source, '_, E>) -> bool,
    terminal_candidate: impl Fn(&mut SynIn<'_, 'source, '_, E>) -> bool,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n' | ';' | ',' | ')' | ']' | '}')
            || safe_boundary(i)
            || terminal_candidate(i)
        {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        if retry_after_error(i) {
            return Some(true);
        }
    }
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

fn parse_operator_name<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<&'source str>
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
fn parse_binding_power<E>(i: SynIn<E>) -> Option<BindingPower>
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
    let table = crate::operator::OperatorTable::empty();
    parse_binding_declaration_with_operators(&table, i)
}

pub(crate) fn parse_binding_declaration_with_operators<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<BindingDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let keyword = i.run(scan_word)?;
    let visibility = visibility_prefix(keyword)?.visibility;
    let binding_base = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
    binding_trivia(binding_base, &mut i)?;
    let stops = i.local.stop_set().unwrap_or_default().with(StopKind::Equal);
    i.local.push_stop_set(stops);
    let target_role = GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Target));
    let target = i.run(from_fn(|i| parse_pattern_with_outer_missing_role(table, Some(target_role), i)));
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    let target = target.map_or(Recovered::Incomplete, Recovered::Complete);
    let mut end = match &target {
        Recovered::Complete(pattern) => pattern.range().end,
        Recovered::Incomplete => i.pos(),
    };

    let definition = {
        let checkpoint = i.checkpoint();
        if binding_trivia(binding_base, &mut i).is_none() {
            i.rollback(checkpoint);
            None
        } else if let Some(equals) = i.run(scan_declaration_exact_equals) {
            let body_start = equals.start;
            let body = parse_binding_body_ast(table, binding_base, &mut i)
                .map_or(Recovered::Incomplete, Recovered::Complete);
            let body_end = match &body {
                Recovered::Complete(BindingBody::Inline { expression }) => expression.range().end,
                Recovered::Complete(BindingBody::Indented { block }) => block.range().end,
                Recovered::Incomplete => i.pos(),
            };
            end = body_end.max(equals.end);
            Some(BindingDefinition { equals, body, range: body_start..end })
        } else {
            i.rollback(checkpoint);
            None
        }
    };

    Some(BindingDeclaration {
        visibility,
        target,
        definition,
        range: start..end,
    })
}

pub(crate) fn parse_mod_declaration_with_operators<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ModDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let first = i.run(scan_word)?;
    let mod_base = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
    let (visibility, mod_keyword) = if let Some(prefix) = visibility_prefix(first) {
        mod_trivia(mod_base, &mut i)?;
        let keyword = i.run(scan_word)?;
        (prefix.visibility, keyword)
    } else {
        (Visibility::Private, first)
    };
    (mod_keyword.text() == "mod").then_some(())?;
    mod_trivia(mod_base, &mut i)?;

    let first_name = i.run(scan_word);
    let (test_marker, name) = match first_name {
        Some(word) if word.text() == "test" => {
            let marker = word;
            let checkpoint = i.checkpoint();
            let trivia = mod_trivia(mod_base, &mut i);
            let anonymous = trivia.is_some() && mod_body_starter_pending(&mut i);
            i.rollback(checkpoint);
            if anonymous {
                (Some(marker), None)
            } else {
                let _ = mod_trivia(mod_base, &mut i);
                let name = i.run(scan_word).map_or(Recovered::Incomplete, Recovered::Complete);
                (Some(marker), Some(name))
            }
        }
        Some(word) => (None, Some(Recovered::Complete(word))),
        None => (None, Some(Recovered::Incomplete)),
    };

    let identity_missing = matches!(name, Some(Recovered::Incomplete));
    let body = parse_mod_body_ast(table, mod_base, !identity_missing, &mut i)
        .map_or(Recovered::Incomplete, Recovered::Complete);
    let end = match &body {
        Recovered::Complete(ModBody::Bodyless { semicolon }) => semicolon.end,
        Recovered::Complete(ModBody::Braced { block }) => block.range().end,
        Recovered::Complete(ModBody::Colon { .. }) => i.pos(),
        Recovered::Incomplete => i.pos(),
    };
    Some(ModDeclaration { visibility, test_marker, name, body, range: start..end })
}

fn parse_mod_inline_statement_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<Statement<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let ambient_scope = i
        .local
        .push_inline_canonical_statement_ambient_scope(
            crate::session::InlineStatementOwnerKind::ModColonBody,
        );
    let statement = i.run(from_fn(|i| parse_canonical_statement(table, i)));
    assert_eq!(i.local.pop_ambient_owner_scope(), Some(ambient_scope));
    statement
}

fn parse_mod_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    mod_base: usize,
    allow_missing_colon_retry: bool,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<ModBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let checkpoint = i.checkpoint();
    let _trivia = mod_trivia(mod_base, i)?;
    let punctuation = i.run(scan_punctuation);
    let Some(punctuation) = punctuation else {
        if !allow_missing_colon_retry {
            i.rollback(checkpoint);
            return None;
        }
        if let Some(statement) = parse_mod_inline_statement_ast(table, i) {
            return Some(ModBody::Colon {
                colon: Recovered::Incomplete,
                body: Recovered::Complete(ModColonBody::Inline { statement: Box::new(statement) }),
            });
        }
        if mod_statement_error_retry_ast(table, i).is_some_and(|retry| retry) {
            let statement = parse_mod_inline_statement_ast(table, i)?;
            return Some(ModBody::Colon {
                colon: Recovered::Incomplete,
                body: Recovered::Complete(ModColonBody::Inline { statement: Box::new(statement) }),
            });
        }
        if i.pos() == start {
            i.rollback(checkpoint);
        }
        return None;
    };
    match punctuation.kind() {
        PunctuationKind::Semicolon => Some(ModBody::Bodyless { semicolon: punctuation.range() }),
        PunctuationKind::Open(Delimiter::Brace) => Some(ModBody::Braced {
            block: parse_braced_statement_block_expression(table, punctuation.range(), i),
        }),
        PunctuationKind::Colon => Some(ModBody::Colon {
            colon: Recovered::Complete(punctuation.range()),
            body: parse_mod_colon_body_ast(table, mod_base, i)
                .map_or(Recovered::Incomplete, Recovered::Complete),
        }),
        _ => {
            i.rollback(checkpoint);
            if !allow_missing_colon_retry {
                return None;
            }
            if let Some(statement) = parse_mod_inline_statement_ast(table, i) {
                return Some(ModBody::Colon {
                    colon: Recovered::Incomplete,
                    body: Recovered::Complete(ModColonBody::Inline { statement: Box::new(statement) }),
                });
            }
            if mod_statement_error_retry_ast(table, i).is_some_and(|retry| retry) {
                let statement = parse_mod_inline_statement_ast(table, i)?;
                return Some(ModBody::Colon {
                    colon: Recovered::Incomplete,
                    body: Recovered::Complete(ModColonBody::Inline { statement: Box::new(statement) }),
                });
            }
            None
        }
    }
}

fn parse_mod_colon_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    mod_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<ModColonBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia)?;
    let has_newline = i.input.source()[trivia.range()].contains(['\r', '\n']);
    if has_newline {
        if i.local.line().line_indent <= mod_base {
            i.rollback(checkpoint);
            return None;
        }
        let block_indent = i.local.line().line_indent;
        return Some(ModColonBody::Indented {
            block: parse_indented_mod_body(table, trivia, mod_base, block_indent, i),
        });
    }
    let ambient_scope = i
        .local
        .push_inline_canonical_statement_ambient_scope(
            crate::session::InlineStatementOwnerKind::ModColonBody,
        );
    let statement = if let Some(statement) = i.run(from_fn(|i| parse_canonical_statement(table, i))) {
        Some(statement)
    } else if mod_statement_error_retry_ast(table, i).is_some_and(|retry| retry) {
        i.run(from_fn(|i| parse_canonical_statement(table, i)))
    } else {
        None
    };
    let body = statement.map(|statement| {
        let terminal = i.checkpoint();
        if i.run(scan_punctuation).is_none_or(|punctuation| punctuation.kind() != PunctuationKind::Semicolon) {
            i.rollback(terminal);
        }
        ModColonBody::Inline { statement: Box::new(statement) }
    });
    assert_eq!(i.local.pop_ambient_owner_scope(), Some(ambient_scope));
    body
}

/// AST parsing keeps recovery diagnostics in the direct-CST channel, but it
/// must consume and retry the same malformed episode so both paths agree on
/// the following statement boundary and the recovered Mod body shape.
fn mod_statement_error_retry_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n' | ';' | ',' | ')' | ']' | '}' | '{' | ':') {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        let checkpoint = i.checkpoint();
        let candidate = i.run(from_fn(|i| parse_canonical_statement(table, i))).is_some();
        i.rollback(checkpoint);
        if candidate {
            return Some(true);
        }
    }
}

fn mod_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| matches!(
        punctuation.kind(),
        PunctuationKind::Semicolon | PunctuationKind::Open(Delimiter::Brace) | PunctuationKind::Colon
    ));
    i.rollback(checkpoint);
    pending
}

fn mod_trivia<E>(mod_base: usize, i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia)?;
    if i.input.source()[trivia.range()].contains(['\r', '\n']) && i.local.line().line_indent <= mod_base {
        i.rollback(checkpoint);
        return None;
    }
    Some(trivia)
}

/// One maximal Struct continuation run. It may cross a newline only when the
/// next line stays inside the baseline captured by the Struct introduction.
fn struct_continuation_trivia<E>(struct_base: usize, i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    mod_trivia(struct_base, i)
}

fn parse_binding_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    binding_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<BindingBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia)?;
    let has_newline = i.input.source()[trivia.range()].contains(['\r', '\n']);
    if has_newline {
        if i.local.line().line_indent <= binding_base {
            i.rollback(checkpoint);
            return None;
        }
        let block_indent = i.local.line().line_indent;
        return Some(BindingBody::Indented {
            block: parse_indented_binding_body(table, trivia, binding_base, block_indent, i),
        });
    }
    let expression = i.run(from_fn(|i| parse_expression_with_operators(table, i)))?;
    Some(BindingBody::Inline { expression })
}

fn binding_trivia<E>(binding_base: usize, i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia)?;
    if i.input.source()[trivia.range()].contains(['\r', '\n'])
        && i.local.line().line_indent <= binding_base
    {
        i.rollback(checkpoint);
        return None;
    }
    Some(trivia)
}

/// Scans a declaration definition introducer only when the entire contiguous
/// operator run is the lone `=` spelling.
fn scan_declaration_exact_equals<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    while i.input.remainder().chars().next().is_some_and(declaration_operator_character) {
        i.input.next()?;
    }
    let end = i.pos();
    if &i.input.source()[start..end] != "=" {
        i.rollback(checkpoint);
        return None;
    }
    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);
    Some(start..end)
}

fn declaration_operator_character(character: char) -> bool {
    !character.is_whitespace()
        && !character.is_ascii_digit()
        && character != '_'
        && !unicode_ident::is_xid_continue(character)
        && !matches!(character, '(' | ')' | '[' | ']' | '{' | '}' | ',' | ':' | '/' | ';' | '\\' | '\'' | '@')
}

pub(crate) fn parse_use_declaration<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<UseDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let first = i.run(scan_word)?;
    let visibility = if let Some(visibility) = visibility_prefix(first) {
        inline_trivia(&mut i)?;
        let keyword = i.run(scan_word)?;
        (keyword.text() == "use").then_some(visibility.visibility)?
    } else {
        (first.text() == "use").then_some(Visibility::Private)?
    };
    inline_trivia(&mut i)?;

    let tree = parse_use_tree(&mut i)?;
    let end = tree.range().end;

    Some(UseDeclaration {
        range: start..end,
        visibility,
        tree,
    })
}

fn parse_use_tree<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<UseTree<'source>>
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

fn parse_use_alias<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<WordSpan<'source>>
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

fn scan_use_version<'source, E>(mut i: SynIn<'_, 'source, '_, E>) -> Option<UseVersion<'source>>
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

fn scan_open_parenthesis<E>(mut i: SynIn<E>) -> Option<Range<usize>>
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

fn parse_close_delimiter<E>(delimiter: Delimiter, mut i: SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Close(delimiter)).then(|| punctuation.range())
}

fn parse_close_brace<E>(mut i: SynIn<E>) -> Option<Range<usize>>
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

fn parse_use_separator<E>(mut i: SynIn<E>) -> Option<UseSeparator>
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
    use chasa::{input::IsCut, prelude::{In, from_fn}};
    use std::{
        cell::RefCell,
        rc::Rc,
        sync::{Arc, mpsc},
        thread,
        time::Duration,
    };

    use crate::{
        SyntaxDiagnostic, SyntaxDiagnosticCause, SyntaxNode,
        input::SourceInput,
        session::{
            AmbientOwnerScopeFrame, CommitOutput, CommittedRecoveryRecord, ExpectedSyntax,
            FullCstOutput, HeaderOutput, IfExpressionCompanionId, ParseLocal, Probe, StopSet,
            TypeDeclarationRole, if_continuation_owner,
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
    const LATE_USE_AFTER_BODY_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/late-use-after-body/main.yu"
    ));
    const MALFORMED_HEADER_FOLLOWED_BY_VALID_HEADER_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/malformed-header-followed-by-valid-header/main.yu"
    ));
    const HEADER_FULL_DIAGNOSTIC_IDENTITY_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/header-full-diagnostic-identity/main.yu"
    ));
    const HEADER_OPERATOR_ORDER_PLUS_THEN_STAR_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/header-operator-order-plus-then-star/main.yu"
    ));
    const HEADER_OPERATOR_ORDER_STAR_THEN_PLUS_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/header-operator-order-star-then-plus/main.yu"
    ));
    const LATE_OPERATOR_AFTER_BODY_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/late-operator-after-body/main.yu"
    ));
    const UNDECLARED_OPERATOR_NUD_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/undeclared-operator-nud/main.yu"
    ));
    const UNDECLARED_OPERATOR_INFIX_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/undeclared-operator-infix/main.yu"
    ));

    #[derive(Clone, Copy)]
    struct Phase2ParserFixture {
        name: &'static str,
        source: &'static [u8],
        reuses_header_recovery: bool,
        recovery_count: usize,
    }

    const PHASE2_PARSER_FIXTURES: [Phase2ParserFixture; 12] = [
        Phase2ParserFixture {
            name: "leading-use-plain",
            source: LEADING_USE_SOURCE,
            reuses_header_recovery: false,
            recovery_count: 0,
        },
        Phase2ParserFixture {
            name: "leading-use-mod",
            source: LEADING_MOD_USE_SOURCE,
            reuses_header_recovery: false,
            recovery_count: 0,
        },
        Phase2ParserFixture {
            name: "leading-use-realm",
            source: LEADING_REALM_USE_SOURCE,
            reuses_header_recovery: false,
            recovery_count: 0,
        },
        Phase2ParserFixture {
            name: "leading-use-band",
            source: LEADING_BAND_USE_SOURCE,
            reuses_header_recovery: false,
            recovery_count: 0,
        },
        Phase2ParserFixture {
            name: "infix-operator-header",
            source: INFIX_OPERATOR_SOURCE,
            reuses_header_recovery: false,
            recovery_count: 0,
        },
        Phase2ParserFixture {
            name: "late-use-after-body",
            source: LATE_USE_AFTER_BODY_SOURCE,
            reuses_header_recovery: false,
            recovery_count: 0,
        },
        Phase2ParserFixture {
            name: "malformed-header-followed-by-valid-header",
            source: MALFORMED_HEADER_FOLLOWED_BY_VALID_HEADER_SOURCE,
            reuses_header_recovery: true,
            recovery_count: 1,
        },
        Phase2ParserFixture {
            name: "header-full-diagnostic-identity",
            source: HEADER_FULL_DIAGNOSTIC_IDENTITY_SOURCE,
            reuses_header_recovery: true,
            recovery_count: 2,
        },
        Phase2ParserFixture {
            name: "header-operator-order-plus-then-star",
            source: HEADER_OPERATOR_ORDER_PLUS_THEN_STAR_SOURCE,
            reuses_header_recovery: false,
            recovery_count: 0,
        },
        Phase2ParserFixture {
            name: "header-operator-order-star-then-plus",
            source: HEADER_OPERATOR_ORDER_STAR_THEN_PLUS_SOURCE,
            reuses_header_recovery: false,
            recovery_count: 0,
        },
        Phase2ParserFixture {
            name: "undeclared-operator-nud",
            source: UNDECLARED_OPERATOR_NUD_SOURCE,
            reuses_header_recovery: false,
            recovery_count: 1,
        },
        Phase2ParserFixture {
            name: "undeclared-operator-infix",
            source: UNDECLARED_OPERATOR_INFIX_SOURCE,
            reuses_header_recovery: false,
            recovery_count: 1,
        },
    ];

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
        let Recovered::Complete(declaration) = commit_operator_header(&mut committed, intro) else {
            panic!("operator continuation should parse the source");
        };
        (declaration, committed.into_output())
    }

    fn parse_recovered_operator<'source>(
        source: &'source str,
    ) -> (
        Recovered<OperatorHeaderDeclaration<'source>>,
        FullCstOutput<'source>,
    ) {
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
        let (intro, mut committed) =
            commit_header_statement(Probe::new(i), FullCstOutput::new(source))
                .expect("source has an operator header introduction");
        let HeaderStatementIntro::Operator(intro) = intro else {
            panic!("source did not select the operator continuation");
        };
        let outcome = commit_operator_header(&mut committed, intro);
        (outcome, committed.into_output())
    }

    fn parse_operator_definition_body<'source>(
        source: &'source str,
        operators: &crate::operator::OperatorTable,
    ) -> (
        OperatorHeaderDeclaration<'source>,
        Recovered<ParsedExpression<rowan::Checkpoint>>,
        FullCstOutput<'source>,
    ) {
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
        let (intro, mut committed) =
            commit_header_statement(Probe::new(i), FullCstOutput::new(source))
                .expect("source has an operator header introduction");
        let HeaderStatementIntro::Operator(intro) = intro else {
            panic!("source did not select the operator continuation");
        };

        committed.start_node(SyntaxKind::Root);
        let Recovered::Complete(header) = commit_operator_header(&mut committed, intro) else {
            panic!("operator header should complete before its body continuation");
        };
        let body = commit_operator_definition_body(operators, &mut committed);

        // The future root loop owns statement separators and following trivia.
        // This focused harness emits only the safe-point tails used below.
        if let Some(tail) = commit_trivia(&mut committed) {
            if !tail.is_empty() {
                committed.emit_trivia(&tail);
            }
        }
        if let Some(semicolon) = commit_character(&mut committed, ';') {
            committed.token(SyntaxKind::Semicolon, semicolon);
        }
        committed.probe(|probe| assert_eq!(probe.input().input.remainder(), ""));
        committed.finish_node();

        (header, body, committed.into_output())
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
        let Recovered::Complete(declaration) = commit_use_declaration(&mut committed, intro) else {
            panic!("use continuation should parse the source");
        };
        (declaration, committed.into_output())
    }

    fn assert_direct_use_incomplete_is_lossless(source: &str) {
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
        let (intro, mut committed) =
            commit_header_statement(Probe::new(i), FullCstOutput::new(source))
                .expect("use keyword commits the header continuation");
        let HeaderStatementIntro::Use(intro) = intro else {
            panic!("expected a use continuation");
        };
        assert!(matches!(
            commit_use_declaration(&mut committed, intro),
            Recovered::Incomplete
        ));
        let root = SyntaxNode::new_root(committed.into_output().finish_complete());
        assert_eq!(root.to_string(), source);
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::Missing)
        );
    }

    fn parse_direct_binding_with_output<'source>(
        source: &'source str,
        operators: &crate::operator::OperatorTable,
    ) -> (
        ParsedBindingDeclaration<'source, rowan::Checkpoint>,
        FullCstOutput<'source>,
    ) {
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
        let Recovered::Complete(declaration) =
            commit_binding_declaration(operators, &mut committed, intro)
        else {
            panic!("complete binding declaration");
        };
        (declaration, committed.into_output())
    }

    fn parse_recovered_binding<'source>(
        source: &'source str,
        operators: &crate::operator::OperatorTable,
    ) -> (
        Recovered<ParsedBindingDeclaration<'source, rowan::Checkpoint>>,
        FullCstOutput<'source>,
    ) {
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
        let outcome = commit_binding_declaration(operators, &mut committed, intro);
        (outcome, committed.into_output())
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

    fn parse_recovered_direct_header(source: &str) -> HeaderOutput {
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
        let (intro, mut committed) = commit_header_statement(Probe::new(i), HeaderOutput::new())
            .expect("source has a direct header declaration introduction");
        match intro {
            HeaderStatementIntro::Use(intro) => {
                let _ = commit_use_declaration(&mut committed, intro);
            }
            HeaderStatementIntro::Operator(intro) => {
                let _ = commit_operator_header(&mut committed, intro);
            }
        }
        committed.into_output()
    }

    fn phase2_fixture_source(fixture: Phase2ParserFixture) -> &'static str {
        std::str::from_utf8(fixture.source).expect("phase-2 parser fixtures are UTF-8")
    }

    fn phase2_fixture_header_recoveries(
        fixture: Phase2ParserFixture,
        source: &str,
    ) -> Vec<CommittedRecoveryRecord> {
        if !fixture.reuses_header_recovery {
            return Vec::new();
        }

        let header_source = source
            .lines()
            .next()
            .expect("recovery fixture has a header line");
        parse_recovered_direct_header(header_source)
            .committed_recoveries()
            .to_vec()
    }

    fn parse_phase2_direct_root(
        source: &str,
        header: &crate::HeaderInfo,
        header_recoveries: &[CommittedRecoveryRecord],
    ) -> DirectRootCandidateOutput {
        let imported = crate::operator::OperatorTable::empty();
        let compilation =
            crate::operator::compile_full_parse_operators_recovering(&imported, header.operators())
                .expect("phase-2 parser fixtures have valid operator spellings");
        parse_direct_root_candidate(source, &compilation.table, header_recoveries)
    }

    fn syntax_range(range: rowan::TextRange) -> Range<usize> {
        u32::from(range.start()) as usize..u32::from(range.end()) as usize
    }

    fn assert_complete_root_tree(fixture: Phase2ParserFixture, source: &str, root: &SyntaxNode) {
        // `parse_direct_root_candidate` can only return after
        // `RowanSink::finish_complete`, which checks its open-node counter.
        // The parent walk makes the resulting closed Rowan tree explicit at
        // the corpus boundary as well.
        assert_eq!(root.kind(), SyntaxKind::Root, "{}", fixture.name);
        assert!(root.parent().is_none(), "{}", fixture.name);
        for node in root.descendants() {
            assert_eq!(
                node.ancestors().last().map(|ancestor| ancestor.kind()),
                Some(SyntaxKind::Root),
                "{} has a detached CST node: {:?}",
                fixture.name,
                node.kind(),
            );
        }

        let mut next_start = 0;
        for token in root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
        {
            let range = syntax_range(token.text_range());
            assert_eq!(
                range.start,
                next_start,
                "{} has a token coverage gap or overlap before {:?}",
                fixture.name,
                token.kind(),
            );
            assert_eq!(
                token.text(),
                &source[range.clone()],
                "{} token text must retain its source range",
                fixture.name,
            );
            next_start = range.end;
        }
        assert_eq!(
            next_start,
            source.len(),
            "{} token coverage must reach EOF",
            fixture.name,
        );
        assert_eq!(root.to_string(), source, "{}", fixture.name);
    }

    fn assert_recovery_diagnostic_identity(
        fixture: Phase2ParserFixture,
        output: &DirectRootCandidateOutput,
        root: &SyntaxNode,
        header_recoveries: &[CommittedRecoveryRecord],
    ) {
        let recoveries = output.committed_recoveries();
        assert_eq!(recoveries.len(), fixture.recovery_count, "{}", fixture.name,);

        let cst_recoveries = root
            .descendants()
            .filter_map(|node| match node.kind() {
                SyntaxKind::Missing => {
                    Some((RecoveryKind::Missing, syntax_range(node.text_range())))
                }
                SyntaxKind::Error => Some((RecoveryKind::Error, syntax_range(node.text_range()))),
                _ => None,
            })
            .collect::<Vec<_>>();
        let committed_recoveries = recoveries
            .iter()
            .map(|recovery| (recovery.kind, recovery.site.range.clone()))
            .collect::<Vec<_>>();
        assert_eq!(cst_recoveries, committed_recoveries, "{}", fixture.name);

        let diagnostics = recoveries
            .iter()
            .cloned()
            .map(SyntaxDiagnostic::recovery)
            .collect::<Vec<_>>();
        assert_eq!(diagnostics.len(), recoveries.len(), "{}", fixture.name);
        for (diagnostic, recovery) in diagnostics.iter().zip(recoveries) {
            let SyntaxDiagnosticCause::Recovery(diagnostic_recovery) = diagnostic.cause() else {
                panic!("{} produced a non-recovery diagnostic", fixture.name);
            };
            assert_eq!(diagnostic.id(), recovery.id.0, "{}", fixture.name);
            assert_eq!(
                diagnostic.primary(),
                &recovery.site.range,
                "{}",
                fixture.name
            );
            assert_eq!(diagnostic_recovery.record(), recovery, "{}", fixture.name);
        }

        for header_recovery in header_recoveries {
            let reused = recoveries
                .iter()
                .find(|recovery| recovery.id == header_recovery.id)
                .expect("full candidate must retain every matching header recovery");
            assert_eq!(reused, header_recovery, "{}", fixture.name);
        }
    }

    fn assert_header_fact_range_parity(
        fixture: Phase2ParserFixture,
        source: &str,
        header: &crate::HeaderInfo,
        root: &SyntaxNode,
    ) {
        for import in header.imports() {
            let range = import.range().clone();
            let declaration_source = &source[range.clone()];
            let (header_declaration, _) =
                parse_direct_header_with_output(declaration_source, HeaderOutput::new());
            let (full_declaration, full_output) = parse_direct_header_with_output(
                declaration_source,
                FullCstOutput::new(declaration_source),
            );
            assert_eq!(header_declaration, full_declaration, "{}", fixture.name);
            assert_eq!(
                full_output.finish_complete().to_string(),
                declaration_source,
                "{}",
                fixture.name,
            );
            let HeaderDeclaration::Use(declaration) = header_declaration else {
                panic!("{} import range did not parse as use", fixture.name);
            };
            let expanded = declaration
                .expand_header_imports()
                .into_iter()
                .collect::<Result<Vec<_>, _>>()
                .expect("fixture import is a complete header fact");
            assert_eq!(expanded, [import.clone()], "{}", fixture.name);
            assert!(
                root.descendants().any(|node| {
                    node.kind() == SyntaxKind::UseDeclaration
                        && syntax_range(node.text_range()) == range
                }),
                "{} full candidate lost header import range {:?}",
                fixture.name,
                import.range(),
            );
        }

        for operator in header.operators() {
            let range = operator.range().clone();
            let declaration_source = &source[range.clone()];
            let (header_declaration, _) =
                parse_direct_header_with_output(declaration_source, HeaderOutput::new());
            let (full_declaration, full_output) = parse_direct_header_with_output(
                declaration_source,
                FullCstOutput::new(declaration_source),
            );
            assert_eq!(header_declaration, full_declaration, "{}", fixture.name);
            assert_eq!(
                full_output.finish_complete().to_string(),
                declaration_source,
                "{}",
                fixture.name,
            );
            let HeaderDeclaration::OperatorHeader(declaration) = header_declaration else {
                panic!(
                    "{} operator range did not parse as an operator header",
                    fixture.name
                );
            };
            let parsed_operator = declaration.to_header_operator();
            assert_eq!(
                parsed_operator.range(),
                &(0..declaration_source.len()),
                "{}",
                fixture.name
            );
            assert_eq!(parsed_operator.name(), operator.name(), "{}", fixture.name);
            assert_eq!(
                parsed_operator.fixity(),
                operator.fixity(),
                "{}",
                fixture.name
            );
            assert_eq!(
                parsed_operator.visibility(),
                operator.visibility(),
                "{}",
                fixture.name
            );
            assert_eq!(
                parsed_operator.is_lazy(),
                operator.is_lazy(),
                "{}",
                fixture.name
            );
            assert_eq!(
                parsed_operator.binding_power(),
                operator.binding_power(),
                "{}",
                fixture.name
            );
            assert!(
                root.descendants().any(|node| {
                    node.kind() == SyntaxKind::OperatorHeader
                        && syntax_range(node.text_range()) == range
                }),
                "{} full candidate lost header operator range {:?}",
                fixture.name,
                operator.range(),
            );
        }
    }

    fn assert_parse_file_matches_direct_candidate(
        fixture: Phase2ParserFixture,
        parsed_root: &SyntaxNode,
        direct_root: &SyntaxNode,
    ) {
        let mut parsed_kinds = parsed_root
            .descendants()
            .map(|node| node.kind())
            .collect::<Vec<_>>();
        parsed_kinds.sort_unstable();
        parsed_kinds.dedup();

        for kind in parsed_kinds {
            let parsed_count = parsed_root
                .descendants()
                .filter(|node| node.kind() == kind)
                .count();
            let direct_count = direct_root
                .descendants()
                .filter(|node| node.kind() == kind)
                .count();
            assert_eq!(
                direct_count, parsed_count,
                "{} public parse diverged from direct candidate for {:?}: parsed {parsed_count}, direct {direct_count}",
                fixture.name, kind,
            );
        }
    }

    #[test]
    fn direct_root_candidate_parses_use_operator_and_binding_in_source_order() {
        let source = "use std::io\ninfix (<+>) 50 51 = left\nmy value = left";
        let output =
            parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let root = SyntaxNode::new_root(output.green().clone());

        assert_eq!(root.kind(), SyntaxKind::Root);
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.children().map(|node| node.kind()).collect::<Vec<_>>(),
            [
                SyntaxKind::UseDeclaration,
                SyntaxKind::OperatorHeader,
                SyntaxKind::OperatorChain,
                SyntaxKind::BindingStatement,
            ],
        );
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error)
        );
    }

    #[test]
    fn root_ambient_scope_is_balanced_after_normal_and_recovery_root_loops() {
        for source in ["struct Marker;", "@\nstruct Marker;"] {
            let mut local = ParseLocal::new();
            let output = parse_direct_root_candidate_with_local(
                source,
                &crate::operator::OperatorTable::empty(),
                &mut local,
            );
            assert_eq!(SyntaxNode::new_root(output.green().clone()).to_string(), source);
            assert_eq!(local.ambient_owner_scope_depth(), 0, "{source:?}");
            assert_eq!(local.ambient_owner_scope(), None, "{source:?}");
        }
    }

    #[test]
    fn mod_inline_ambient_scope_is_balanced_after_ast_and_direct_bodies() {
        let source = "mod outer: my item = value;";
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let table = crate::operator::OperatorTable::empty();
        i.run(from_fn(|i| parse_mod_declaration_with_operators(&table, i)))
            .expect("Mod inline AST body");
        assert_eq!(i.input.remainder(), "");
        assert_eq!(i.local.ambient_owner_scope_depth(), 0);

        let source = "mod outer: @my item = value;";
        let mut local = ParseLocal::new();
        let output = parse_direct_root_candidate_with_local(
            source,
            &crate::operator::OperatorTable::empty(),
            &mut local,
        );
        assert_eq!(SyntaxNode::new_root(output.green().clone()).to_string(), source);
        assert_eq!(local.ambient_owner_scope_depth(), 0);
    }

    #[test]
    fn direct_root_candidate_parses_all_fixities_and_operator_aware_bindings_to_eof() {
        let source = concat!(
            "use std::io\n",
            "nullfix (!) = !\n",
            "prefix (+) 70 = +!a\n",
            "suffix (++) 90 = a++\n",
            "infix (+!) 50 51 = a+!b\n",
            "my value = a+!b",
        );
        let output = parse_direct_root_candidate(source, &root_candidate_operator_table(), &[]);
        let root = SyntaxNode::new_root(output.green().clone());

        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            Vec::<String>::new(),
        );
        for kind in [
            SyntaxKind::UseDeclaration,
            SyntaxKind::OperatorHeader,
            SyntaxKind::BindingStatement,
            SyntaxKind::OperatorChain,
            SyntaxKind::IdentifierExpression,
            SyntaxKind::PrefixOperatorUse,
            SyntaxKind::NullfixOperatorUse,
            SyntaxKind::SuffixOperatorUse,
            SyntaxKind::InfixOperatorUse,
        ] {
            assert!(
                root.descendants().any(|node| node.kind() == kind),
                "missing {kind:?} in direct root candidate output",
            );
        }
    }

    #[test]
    fn direct_root_candidate_recovers_one_unknown_line_then_continues() {
        let source = "unknown words\nuse std::io";
        let output =
            parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let root = SyntaxNode::new_root(output.green().clone());

        assert_eq!(root.to_string(), source);
        let errors = root
            .children()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].text().to_string(), "unknown words");
        assert!(
            root.children()
                .any(|node| node.kind() == SyntaxKind::UseDeclaration)
        );
    }

    #[test]
    fn direct_root_recovery_records_become_one_diagnostic_per_cst_node_and_reuse_header_records() {
        let source = "use";
        let header_output = parse_recovered_direct_header(source);
        let header_recoveries = header_output.committed_recoveries();
        let [header_recovery] = header_recoveries else {
            panic!("the incomplete header declaration must commit one recovery");
        };

        let output = parse_direct_root_candidate(
            source,
            &crate::operator::OperatorTable::empty(),
            header_recoveries,
        );
        let root = SyntaxNode::new_root(output.green().clone());
        let full_recoveries = output.committed_recoveries();
        let diagnostics = full_recoveries
            .iter()
            .cloned()
            .map(SyntaxDiagnostic::recovery)
            .collect::<Vec<_>>();

        let cst_recovery_nodes = root
            .descendants()
            .filter_map(|node| match node.kind() {
                SyntaxKind::Missing => Some((RecoveryKind::Missing, node.text_range())),
                SyntaxKind::Error => Some((RecoveryKind::Error, node.text_range())),
                _ => None,
            })
            .collect::<Vec<_>>();
        let committed_nodes = full_recoveries
            .iter()
            .map(|record| {
                (
                    record.kind,
                    rowan::TextRange::new(
                        (record.site.range.start as u32).into(),
                        (record.site.range.end as u32).into(),
                    ),
                )
            })
            .collect::<Vec<_>>();

        assert_eq!(root.to_string(), source);
        assert_eq!(cst_recovery_nodes, committed_nodes);
        assert_eq!(diagnostics.len(), full_recoveries.len());
        for (diagnostic, record) in diagnostics.iter().zip(full_recoveries) {
            let SyntaxDiagnosticCause::Recovery(recovery) = diagnostic.cause() else {
                panic!("every committed recovery must produce a recovery diagnostic");
            };
            assert_eq!(recovery.record(), record);
        }

        let [full_recovery] = full_recoveries else {
            panic!("the full root candidate must preserve the header recovery");
        };
        assert_eq!(full_recovery.id, header_recovery.id);
        assert_eq!(full_recovery.site, header_recovery.site);
        assert_eq!(full_recovery.expectations, header_recovery.expectations);
        assert!(Arc::ptr_eq(
            &full_recovery.expectations,
            &header_recovery.expectations
        ));
        assert_eq!(
            full_recovery.primary_expectation,
            header_recovery.primary_expectation
        );
    }

    #[test]
    fn direct_root_candidate_keeps_embedded_fake_boundaries_in_one_error_episode() {
        let source = concat!(
            "garbage \"string;\nuse hidden\" /* comment;\nuse hidden */ ",
            "'[yumark;\nuse hidden] '{\n```raw\nfence;\nuse hidden\n```\n}\n",
            "use std::io",
        );
        let output =
            parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let root = SyntaxNode::new_root(output.green().clone());

        assert_eq!(root.to_string(), source);
        let errors = root
            .children()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1);
        assert!(errors[0].text().to_string().contains("fence;\nuse hidden"));
        assert!(
            root.children()
                .any(|node| node.kind() == SyntaxKind::UseDeclaration)
        );
    }

    #[test]
    fn direct_root_candidate_keeps_heredoc_interpolation_and_rule_boundaries_in_one_error() {
        let source = concat!(
            "garbage \"\"\"heredoc;\nuse hidden\"\"\" ",
            "\"string %{interpolation;\nuse hidden}\" ",
            "~\"rule;\nuse hidden\"\n",
            "use std::io",
        );
        let output =
            parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let root = SyntaxNode::new_root(output.green().clone());
        let errors = root
            .children()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();

        assert_eq!(root.to_string(), source);
        assert_eq!(errors.len(), 1);
        assert!(
            errors[0]
                .text()
                .to_string()
                .contains("interpolation;\nuse hidden")
        );
        assert!(errors[0].text().to_string().contains("rule;\nuse hidden"));
        assert!(
            root.children()
                .any(|node| node.kind() == SyntaxKind::UseDeclaration)
        );
    }

    #[test]
    fn direct_root_candidate_handles_every_byte_prefix_without_invalid_recovery_shapes() {
        let valid_sources = [
            "use std::io\nmy value = 1",
            "prefix (+) 70 = +!a\ninfix (+!) 50 51 = a+!b\nmy value = a+!b",
            "nullfix (!) = !\nsuffix (++) 90 = a++",
        ];

        for source in valid_sources {
            assert!(source.is_ascii(), "prefix corpus must be byte-sliceable");
            for prefix_len in 0..=source.len() {
                assert_direct_root_terminates_with_valid_recovery_shapes(
                    source[..prefix_len].to_owned(),
                );
            }
        }
    }

    #[test]
    fn direct_root_candidate_handles_representative_malformed_sources_without_invalid_recovery_shapes()
     {
        for source in [
            "garbage; use std::io",
            "use",
            "prefix (+) 70",
            "my value =",
            "infix (<+>) 50 51 = @@\nmy value = 1",
            "garbage \"unterminated",
        ] {
            assert_direct_root_terminates_with_valid_recovery_shapes(source.to_owned());
        }
    }

    #[test]
    fn parse_file_matches_direct_candidate_for_binding_and_integer_projection() {
        let source: Arc<crate::SourceText> = Arc::from("use std::io\nmy value = 123\n");
        let header = Arc::new(crate::scan_header(Arc::clone(&source)));
        let parsed = crate::parse_file(
            Arc::clone(&source),
            header,
            Arc::new(crate::SyntaxEnvironment::empty()),
        );
        let parsed_root = SyntaxNode::new_root(parsed.green().clone());
        let direct_root = SyntaxNode::new_root(
            parse_direct_root_candidate(
                source.as_ref(),
                &crate::operator::OperatorTable::empty(),
                &[],
            )
            .green()
            .clone(),
        );

        assert_eq!(parsed_root.to_string(), source.as_ref());
        assert_eq!(direct_root.to_string(), source.as_ref());
        for kind in [SyntaxKind::BindingStatement, SyntaxKind::IntegerLiteral] {
            assert!(parsed_root.descendants().any(|node| node.kind() == kind));
            assert!(direct_root.descendants().any(|node| node.kind() == kind));
        }
    }

    #[test]
    fn direct_root_candidate_meets_gate_8_for_every_phase2_parser_fixture() {
        for fixture in PHASE2_PARSER_FIXTURES {
            let source = phase2_fixture_source(fixture);
            let source_text: Arc<crate::SourceText> = Arc::from(source);
            let header = Arc::new(crate::scan_header(Arc::clone(&source_text)));
            let header_recoveries = phase2_fixture_header_recoveries(fixture, source);
            let output = parse_phase2_direct_root(source, header.as_ref(), &header_recoveries);
            let root = SyntaxNode::new_root(output.green().clone());

            assert_complete_root_tree(fixture, source, &root);
            assert_header_fact_range_parity(fixture, source, header.as_ref(), &root);
            assert_recovery_diagnostic_identity(fixture, &output, &root, &header_recoveries);
        }
    }

    #[test]
    fn parse_file_matches_direct_root_candidate_for_every_phase2_parser_fixture() {
        for fixture in PHASE2_PARSER_FIXTURES {
            let source = phase2_fixture_source(fixture);
            let source_text: Arc<crate::SourceText> = Arc::from(source);
            let header = Arc::new(crate::scan_header(Arc::clone(&source_text)));
            let parsed = crate::parse_file(
                Arc::clone(&source_text),
                Arc::clone(&header),
                Arc::new(crate::SyntaxEnvironment::empty()),
            );
            let header_recoveries = phase2_fixture_header_recoveries(fixture, source);
            let output = parse_phase2_direct_root(source, header.as_ref(), &header_recoveries);
            let parsed_root = SyntaxNode::new_root(parsed.green().clone());
            let direct_root = SyntaxNode::new_root(output.green().clone());

            assert_complete_root_tree(fixture, source, &parsed_root);
            assert_complete_root_tree(fixture, source, &direct_root);
            assert_parse_file_matches_direct_candidate(fixture, &parsed_root, &direct_root);
        }
    }

    #[test]
    fn header_full_diagnostic_identity_keeps_only_closing_expectation_after_empty_parentheses() {
        let source =
            std::str::from_utf8(HEADER_FULL_DIAGNOSTIC_IDENTITY_SOURCE).expect("fixture is UTF-8");
        let source_text: Arc<crate::SourceText> = Arc::from(source);
        let header = Arc::new(crate::scan_header(Arc::clone(&source_text)));
        let header_recoveries = parse_recovered_direct_header("use")
            .committed_recoveries()
            .to_vec();
        let output = parse_phase2_direct_root(source, header.as_ref(), &header_recoveries);

        let [import_path, closing_parenthesis] = output.committed_recoveries() else {
            panic!("fixture must produce exactly the header and closing recoveries");
        };
        assert_eq!(import_path.site.range, 3..3);
        assert_eq!(closing_parenthesis.kind, RecoveryKind::Missing);
        assert_eq!(closing_parenthesis.site.range, 26..26);
        assert_eq!(
            closing_parenthesis.site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::ExpressionGroup,
                delimiter: Delimiter::Parenthesis,
            }
        );
        assert_eq!(closing_parenthesis.expectations.len(), 1);
        assert_eq!(
            closing_parenthesis.expectations[0].expected,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                Delimiter::Parenthesis,
            ))
        );
    }

    #[test]
    fn header_operator_declaration_order_does_not_change_body_pratt_shape() {
        let fixtures = [
            (
                "plus-then-star",
                HEADER_OPERATOR_ORDER_PLUS_THEN_STAR_SOURCE,
                ["<+>", "<*>"],
            ),
            (
                "star-then-plus",
                HEADER_OPERATOR_ORDER_STAR_THEN_PLUS_SOURCE,
                ["<*>", "<+>"],
            ),
        ];
        let mut body_shapes = Vec::new();

        for (name, bytes, header_names) in fixtures {
            let source = std::str::from_utf8(bytes).expect("fixtures are UTF-8");
            let source_text: Arc<crate::SourceText> = Arc::from(source);
            let header = Arc::new(crate::scan_header(Arc::clone(&source_text)));
            let parsed = crate::parse_file(
                Arc::clone(&source_text),
                Arc::clone(&header),
                Arc::new(crate::SyntaxEnvironment::empty()),
            );
            let root = SyntaxNode::new_root(parsed.green().clone());
            let value_start = source
                .rfind("a <+> b <*> c")
                .expect("fixture has the shared body expression");

            assert_eq!(
                header.coverage().stop(),
                crate::HeaderStop::FirstNonHeader,
                "{name}"
            );
            assert_eq!(
                header.coverage().range(),
                &(0..value_start - "my value = ".len()),
                "{name}"
            );
            assert_eq!(
                header
                    .operators()
                    .iter()
                    .map(|operator| operator.name())
                    .collect::<Vec<_>>(),
                header_names,
                "{name}",
            );
            assert!(parsed.diagnostics().is_empty(), "{name}");

            let shape = root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::OperatorChain)
                .filter(|node| syntax_range(node.text_range()).start >= value_start)
                .map(|node| {
                    let range = syntax_range(node.text_range());
                    range.start - value_start..range.end - value_start
                })
                .collect::<Vec<_>>();
            assert_eq!(shape, [0..13], "{name}");

            let operators = root
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| {
                    token.kind() == SyntaxKind::Operator
                        && syntax_range(token.text_range()).start >= value_start
                })
                .map(|token| token.text().to_owned())
                .collect::<Vec<_>>();
            assert_eq!(operators, ["<+>", "<*>"], "{name}");
            body_shapes.push(shape);
        }

        assert_eq!(body_shapes[0], body_shapes[1]);
    }

    #[test]
    fn operator_declaration_after_header_cutoff_cannot_authorize_later_operator_use() {
        let source =
            std::str::from_utf8(LATE_OPERATOR_AFTER_BODY_SOURCE).expect("fixture is UTF-8");
        let source_text: Arc<crate::SourceText> = Arc::from(source);
        let header = Arc::new(crate::scan_header(Arc::clone(&source_text)));
        let parsed = crate::parse_file(
            Arc::clone(&source_text),
            Arc::clone(&header),
            Arc::new(crate::SyntaxEnvironment::empty()),
        );
        let root = SyntaxNode::new_root(parsed.green().clone());
        let late_use_start = source
            .rfind("<+>")
            .expect("fixture has a late operator use");
        let late_use_end = source[late_use_start..]
            .find('\n')
            .map_or(source.len(), |offset| late_use_start + offset);

        assert_eq!(header.coverage().stop(), crate::HeaderStop::FirstNonHeader);
        assert_eq!(header.coverage().range(), &(0..0));
        assert!(header.operators().is_empty());
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::OperatorHeader)
        );
        assert!(root.descendants().any(|node| node.kind() == SyntaxKind::OperatorChain));
        assert!(
            !root
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| {
                    token.kind() == SyntaxKind::Operator
                        && syntax_range(token.text_range()) == (late_use_start..late_use_start + 3)
                })
        );

        let error_range = late_use_start..late_use_end;
        assert!(root.descendants().any(|node| {
            node.kind() == SyntaxKind::Error && syntax_range(node.text_range()) == error_range
        }));
        assert!(
            parsed
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.primary() == &error_range)
        );
    }

    #[test]
    fn undeclared_operator_in_nud_position_uses_binding_value_recovery() {
        let source = std::str::from_utf8(UNDECLARED_OPERATOR_NUD_SOURCE).expect("fixture is UTF-8");
        let output =
            parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let root = SyntaxNode::new_root(output.green().clone());
        let [recovery] = output.committed_recoveries() else {
            panic!("the NUD fixture must produce one generic recovery");
        };

        assert_eq!(root.to_string(), source);
        assert_eq!(recovery.kind, RecoveryKind::Error);
        assert_eq!(recovery.site.range, 11..15);
        assert_eq!(
            recovery.site.role,
            GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Body))
        );
        let source_text: Arc<crate::SourceText> = Arc::from(source);
        let parsed = crate::parse_file(
            Arc::clone(&source_text),
            Arc::new(crate::scan_header(Arc::clone(&source_text))),
            Arc::new(crate::SyntaxEnvironment::empty()),
        );
        assert_eq!(parsed.diagnostics().len(), 1);
        assert_eq!(parsed.diagnostics()[0].primary(), &(11..15));
        assert!(matches!(
            parsed.diagnostics()[0].cause(),
            SyntaxDiagnosticCause::Recovery(_)
        ));
        assert!(root.descendants().any(|node| {
            node.kind() == SyntaxKind::Error && syntax_range(node.text_range()) == (11..15)
        }));
        assert!(root.descendants().any(|node| {
            node.kind() == SyntaxKind::IdentifierExpression
                && syntax_range(node.text_range()) == (15..20)
        }));
        assert!(
            !root
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Operator)
        );
    }

    #[test]
    fn undeclared_operator_after_left_operand_uses_root_trailing_input_recovery() {
        let source =
            std::str::from_utf8(UNDECLARED_OPERATOR_INFIX_SOURCE).expect("fixture is UTF-8");
        let output =
            parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let root = SyntaxNode::new_root(output.green().clone());
        let [recovery] = output.committed_recoveries() else {
            panic!("the infix fixture must produce one generic recovery");
        };

        assert_eq!(root.to_string(), source);
        assert_eq!(recovery.kind, RecoveryKind::Error);
        assert_eq!(recovery.site.range, 16..25);
        assert_eq!(
            recovery.site.role,
            GrammarRole::Statement(StatementRole::TrailingInput {
                owner: StatementKind::BindingDeclaration,
            })
        );
        let source_text: Arc<crate::SourceText> = Arc::from(source);
        let parsed = crate::parse_file(
            Arc::clone(&source_text),
            Arc::new(crate::scan_header(Arc::clone(&source_text))),
            Arc::new(crate::SyntaxEnvironment::empty()),
        );
        assert_eq!(parsed.diagnostics().len(), 1);
        assert_eq!(parsed.diagnostics()[0].primary(), &(16..25));
        assert!(matches!(
            parsed.diagnostics()[0].cause(),
            SyntaxDiagnosticCause::Recovery(_)
        ));
        assert!(root.descendants().any(|node| {
            node.kind() == SyntaxKind::Error && syntax_range(node.text_range()) == (16..25)
        }));
        assert!(root.descendants().any(|node| node.kind() == SyntaxKind::OperatorChain));
        assert!(
            !root
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Operator)
        );
    }

    fn root_candidate_operator_table() -> crate::operator::OperatorTable {
        crate::operator::OperatorTable::from_declarations([
            crate::operator::OperatorDeclaration::new(
                "+!",
                crate::operator::OperatorFixities::new().with_infix(
                    crate::operator::BindingPower::scalar(50),
                    crate::operator::BindingPower::scalar(51),
                ),
            ),
            crate::operator::OperatorDeclaration::new(
                "+",
                crate::operator::OperatorFixities::new()
                    .with_prefix(crate::operator::BindingPower::scalar(70)),
            ),
            crate::operator::OperatorDeclaration::new(
                "!",
                crate::operator::OperatorFixities::new()
                    .with_prefix(crate::operator::BindingPower::scalar(80))
                    .with_nullfix(),
            ),
            crate::operator::OperatorDeclaration::new(
                "++",
                crate::operator::OperatorFixities::new()
                    .with_suffix(crate::operator::BindingPower::scalar(90)),
            ),
        ])
        .expect("root candidate operator table")
    }

    fn assert_direct_root_terminates_with_valid_recovery_shapes(source: String) {
        let (sender, receiver) = mpsc::channel();
        let handle = thread::spawn(move || {
            let result = std::panic::catch_unwind(|| {
                let root = SyntaxNode::new_root(
                    parse_direct_root_candidate(&source, &root_candidate_operator_table(), &[])
                        .green()
                        .clone(),
                );
                assert_eq!(root.to_string(), source);
                for node in root.descendants() {
                    match node.kind() {
                        SyntaxKind::Missing => assert!(node.text_range().is_empty()),
                        SyntaxKind::Error => assert!(!node.text_range().is_empty()),
                        _ => {}
                    }
                }
            });
            let _ = sender.send(result.map_err(|_| "candidate panicked".to_owned()));
        });

        let result = receiver
            .recv_timeout(Duration::from_secs(1))
            .expect("direct root candidate exceeded the one-second prefix step bound");
        handle.join().expect("candidate worker thread panicked");
        result.expect("direct root candidate violated a lossless recovery invariant");
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

        assert!(
            commit_header_statement(
                Probe::new(i),
                RecordingOutput {
                    calls: Rc::clone(&calls),
                },
            )
            .is_none()
        );
        assert!(calls.borrow().is_empty());
        assert_eq!(source_input.remainder(), source);
    }

    #[test]
    fn statement_intro_selects_use_and_operator_continuations_without_emitting() {
        for (source, expected_remainder) in
            [("our use std", "std"), ("pub lazy infix (<+>)", "(<+>)")]
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
                    assert_eq!(intro.fixity_keyword.map(|word| word.text()), Some("infix"));
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
    fn direct_binding_declaration_emits_one_operator_aware_body_subtree() {
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
        assert!(matches!(binding.target(), Recovered::Complete(target) if target.range() == (3..8)));
        assert!(matches!(binding.definition(), Some(definition)
            if matches!(definition.body(), Recovered::Complete(body) if body.range() == (11..19))));
        assert_eq!(root.kind(), SyntaxKind::BindingStatement);
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter_map(|node| (node.kind() == SyntaxKind::PrefixOperatorUse).then_some(node))
                .count(),
            1
        );
    }

    #[test]
    fn direct_binding_and_operator_body_share_operator_chain_authority() {
        let operators = root_candidate_operator_table();
        let cases = [
            ("value", SyntaxKind::OperatorChain),
            ("123", SyntaxKind::OperatorChain),
            ("+!a", SyntaxKind::OperatorChain),
            ("!", SyntaxKind::OperatorChain),
            ("a++", SyntaxKind::OperatorChain),
            ("a+!b", SyntaxKind::OperatorChain),
        ];

        for (value, kind) in cases {
            let binding_source = format!("my value = {value}");
            let (_, binding_output) = parse_direct_binding_with_output(&binding_source, &operators);
            let binding_root = SyntaxNode::new_root(binding_output.finish_complete());
            assert_eq!(binding_root.to_string(), binding_source);
            assert!(
                binding_root.descendants().any(|node| node.kind() == kind),
                "binding value {value:?} did not emit {kind:?}",
            );

            let operator_source = format!("infix (<+>) 50 51 = {value}");
            let (_, body, operator_output) =
                parse_operator_definition_body(&operator_source, &operators);
            assert!(
                matches!(body, Recovered::Complete(_)),
                "{operator_source:?}"
            );
            let operator_root = SyntaxNode::new_root(operator_output.finish_complete());
            assert_eq!(operator_root.to_string(), operator_source);
            assert!(
                operator_root.descendants().any(|node| node.kind() == kind),
                "operator body {value:?} did not emit {kind:?}",
            );
        }
    }

    #[test]
    fn direct_binding_missing_body_closes_the_statement_and_emits_one_missing_node() {
        let source = "my value =";
        let operators = crate::operator::OperatorTable::empty();
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

        assert!(matches!(
            commit_binding_declaration(&operators, &mut committed, intro),
            Recovered::Complete(_)
        ));
        let root = SyntaxNode::new_root(committed.into_output().finish_complete());
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1
        );
    }

    #[test]
    fn direct_binding_missing_target_uses_the_binding_owner_role() {
        for (source, at) in [("my", 2), ("our", 3), ("pub", 3)] {
            let output = parse_direct_root_candidate(
                source,
                &crate::operator::OperatorTable::empty(),
                &[],
            );
            let [recovery] = output.committed_recoveries() else {
                panic!("missing target must create one recovery for {source:?}");
            };
            assert_eq!(recovery.kind, RecoveryKind::Missing, "{source:?}");
            assert_eq!(
                recovery.site.role,
                GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Target)),
                "{source:?}",
            );
            assert_eq!(recovery.site.range, at..at, "{source:?}");
            assert_eq!(
                recovery.expectations.as_ref(),
                [SyntaxExpectation {
                    role: GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Target)),
                    expected: ExpectedSyntax::Pattern,
                    range: at..at,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }],
                "{source:?}",
            );
        }
    }

    #[test]
    fn direct_use_missing_target_closes_the_declaration_and_emits_one_missing_node() {
        let source = "use";
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
        let (intro, mut committed) =
            commit_header_statement(Probe::new(i), FullCstOutput::new(source))
                .expect("use keyword commits the header continuation");
        let HeaderStatementIntro::Use(intro) = intro else {
            panic!("expected a use continuation");
        };

        assert!(matches!(
            commit_use_declaration(&mut committed, intro),
            Recovered::Incomplete
        ));
        let root = SyntaxNode::new_root(committed.into_output().finish_complete());
        assert_eq!(root.kind(), SyntaxKind::UseDeclaration);
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
        );
    }

    #[test]
    fn direct_use_recovers_missing_operator_alias_exclusion_and_anchor_slots() {
        for source in [
            "use (",
            "use (+",
            "use std as",
            "use std::* without",
            "use std with",
        ] {
            assert_direct_use_incomplete_is_lossless(source);
        }
    }

    #[test]
    fn direct_use_exclusion_group_discards_a_mismatched_close_before_its_matching_close() {
        let source = "use std::* without {foo)}";
        let (_, output) = parse_direct_use_with_output(source, FullCstOutput::new(source));
        let root = SyntaxNode::new_root(output.finish_complete());

        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
        );
    }

    #[test]
    fn direct_use_target_error_retries_a_later_tree_candidate() {
        let source = "use @value";
        let (_, output) = parse_direct_use_with_output(source, FullCstOutput::new(source));
        let root = SyntaxNode::new_root(output.finish_complete());

        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
        );
    }

    #[test]
    fn direct_use_group_missing_close_closes_the_group_at_eof() {
        let source = "use {value";
        let (_, output) = parse_direct_use_with_output(source, FullCstOutput::new(source));
        let root = SyntaxNode::new_root(output.finish_complete());

        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
        );
    }

    #[test]
    fn direct_use_group_recovers_a_missing_same_line_comma() {
        let source = "use {first second}";
        let (declaration, output) =
            parse_direct_use_with_output(source, FullCstOutput::new(source));
        let root = SyntaxNode::new_root(output.finish_complete());

        assert_eq!(root.to_string(), source);
        assert_eq!(declaration.tree().range(), 4..source.len());
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
        );
    }

    #[test]
    fn direct_use_group_discards_a_mismatched_close_before_its_matching_close() {
        let source = "use {value)}";
        let (_, output) = parse_direct_use_with_output(source, FullCstOutput::new(source));
        let root = SyntaxNode::new_root(output.finish_complete());

        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
        );
    }

    #[test]
    fn direct_binding_allows_an_adjacent_exact_definition_introducer() {
        let source = "my value=result";
        let (binding, output) =
            parse_direct_binding_with_output(source, &crate::operator::OperatorTable::empty());
        let root = SyntaxNode::new_root(output.finish_complete());

        assert_eq!(binding.range(), 0..source.len());
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            0,
        );
    }

    #[test]
    fn direct_binding_value_error_retries_a_later_nud_candidate() {
        let source = "my value = @@result";
        let (outcome, output) =
            parse_recovered_binding(source, &crate::operator::OperatorTable::empty());
        let root = SyntaxNode::new_root(output.finish_complete());

        assert!(matches!(outcome, Recovered::Complete(_)));
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
        );
    }

    #[test]
    fn direct_binding_body_error_stops_at_its_safe_point_without_a_candidate() {
        let source = "my value = @@";
        let (outcome, output) =
            parse_recovered_binding(source, &crate::operator::OperatorTable::empty());
        let root = SyntaxNode::new_root(output.finish_complete());

        assert!(matches!(outcome, Recovered::Complete(_)));
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
        );
    }

    #[test]
    fn direct_operator_definition_body_is_a_root_sibling_after_a_complete_header() {
        let source = "infix (<+>) 50 51 = left";
        let (header, body, output) =
            parse_operator_definition_body(source, &crate::operator::OperatorTable::empty());
        let Recovered::Complete(body) = body else {
            panic!("operator definition body should parse");
        };

        assert_eq!(header.range(), 0..19);
        assert_eq!(body.range(), 20..source.len());
        assert!(output.committed_recoveries().is_empty());

        let root = SyntaxNode::new_root(output.finish_complete());
        assert_eq!(root.kind(), SyntaxKind::Root);
        assert_eq!(root.to_string(), source);
        let children = root.children().collect::<Vec<_>>();
        assert_eq!(
            children.iter().map(|node| node.kind()).collect::<Vec<_>>(),
            [SyntaxKind::OperatorHeader, SyntaxKind::OperatorChain],
        );
        assert_eq!(children[0].text().to_string(), "infix (<+>) 50 51 =");
        assert_eq!(children[1].text().to_string(), "left");
    }

    #[test]
    fn direct_operator_definition_body_recovers_missing_inline_trivia_before_a_nud() {
        let source = "infix (<+>) 50 51 =left";
        let (_, body, output) =
            parse_operator_definition_body(source, &crate::operator::OperatorTable::empty());
        assert!(matches!(body, Recovered::Complete(_)));
        assert_eq!(output.committed_recoveries().len(), 1);
        let recovery = &output.committed_recoveries()[0];
        assert_eq!(recovery.kind, RecoveryKind::Missing);
        assert_eq!(
            recovery.site.role,
            GrammarRole::Layout(LayoutRole::InlineTrivia),
        );
        assert_eq!(recovery.site.range, 19..19);

        let root = SyntaxNode::new_root(output.finish_complete());
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
        );
    }

    #[test]
    fn direct_operator_definition_missing_body_keeps_the_complete_header() {
        let header_source = "infix (<+>) 50 51 =";

        for suffix in ["", ";", "\n"] {
            let source = format!("{header_source}{suffix}");
            let (header, body, output) =
                parse_operator_definition_body(&source, &crate::operator::OperatorTable::empty());

            assert!(matches!(body, Recovered::Incomplete), "{source:?}");
            assert_eq!(header.range(), 0..header_source.len(), "{source:?}");
            assert_eq!(output.committed_recoveries().len(), 1, "{source:?}");
            let recovery = &output.committed_recoveries()[0];
            assert_eq!(recovery.kind, RecoveryKind::Missing, "{source:?}");
            assert_eq!(
                recovery.site.role,
                GrammarRole::Statement(StatementRole::OperatorDefinitionBody),
                "{source:?}",
            );
            assert_eq!(
                recovery.site.range,
                header_source.len()..header_source.len(),
                "{source:?}",
            );

            let root = SyntaxNode::new_root(output.finish_complete());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::Missing)
                    .count(),
                1,
                "{source:?}",
            );
            let children = root.children().collect::<Vec<_>>();
            assert_eq!(children[0].kind(), SyntaxKind::OperatorHeader, "{source:?}");
            assert_eq!(children[0].text().to_string(), header_source, "{source:?}");
        }
    }

    #[test]
    fn direct_operator_definition_body_error_retries_a_later_nud_without_changing_header() {
        let header_source = "infix (<+>) 50 51 =";
        let (expected_header, _) =
            parse_direct_operator_with_output(header_source, HeaderOutput::new());
        let source = format!("{header_source} @@left");
        let (header, body, output) =
            parse_operator_definition_body(&source, &crate::operator::OperatorTable::empty());
        let Recovered::Complete(body) = body else {
            panic!("body should retry from the later identifier");
        };

        assert_eq!(header, expected_header);
        assert_eq!(header.range(), 0..header_source.len());
        assert_eq!(body.range(), header_source.len() + 3..source.len());
        assert_eq!(output.committed_recoveries().len(), 1);
        let recovery = &output.committed_recoveries()[0];
        assert_eq!(recovery.kind, RecoveryKind::Error);
        assert_eq!(
            recovery.site.role,
            GrammarRole::Statement(StatementRole::OperatorDefinitionBody),
        );
        assert_eq!(
            recovery.site.range,
            header_source.len() + 1..header_source.len() + 3
        );

        let root = SyntaxNode::new_root(output.finish_complete());
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            ["@@"],
        );
        assert_eq!(
            root.children().map(|node| node.kind()).collect::<Vec<_>>(),
            [
                SyntaxKind::OperatorHeader,
                SyntaxKind::Error,
                SyntaxKind::OperatorChain,
            ],
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

        let (_, full_output) =
            parse_direct_operator_with_output(source, FullCstOutput::new(source));
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
                declaration
                    .left_binding_power()
                    .map(BindingPower::components),
                left,
                "{source}"
            );
            assert_eq!(
                declaration
                    .right_binding_power()
                    .map(BindingPower::components),
                right,
                "{source}"
            );
            assert_eq!(output.finish_complete().to_string(), source, "{source}");
        }
    }

    #[test]
    fn direct_operator_header_missing_name_preserves_its_binding_power_and_equals() {
        let source = "prefix 50 =";
        let (outcome, output) = parse_recovered_operator(source);
        let root = SyntaxNode::new_root(output.finish_complete());

        assert!(matches!(outcome, Recovered::Incomplete));
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
        );
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::BindingPower)
        );
    }

    #[test]
    fn direct_operator_header_unterminated_name_closes_its_node_and_preserves_following_slots() {
        let source = "prefix (+ 50 =";
        let (outcome, output) = parse_recovered_operator(source);
        let root = SyntaxNode::new_root(output.finish_complete());

        assert!(matches!(outcome, Recovered::Incomplete));
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
        );
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::OperatorName)
        );
    }

    #[test]
    fn direct_operator_header_missing_fixity_does_not_guess_an_arity() {
        let source = "lazy";
        let (outcome, output) = parse_recovered_operator(source);
        let root = SyntaxNode::new_root(output.finish_complete());

        assert!(matches!(outcome, Recovered::Incomplete));
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
        );
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::BindingPower)
        );
    }

    #[test]
    fn direct_operator_header_recovers_missing_or_malformed_binding_power_for_every_fixity() {
        let cases = [
            ("nullfix (+) 1 =", SyntaxKind::Error),
            ("prefix (+) =", SyntaxKind::Missing),
            ("suffix (+) 128 =", SyntaxKind::Error),
            ("infix (+) 1. =", SyntaxKind::Error),
        ];

        for (source, recovery_kind) in cases {
            let (outcome, output) = parse_recovered_operator(source);
            let root = SyntaxNode::new_root(output.finish_complete());

            assert!(matches!(outcome, Recovered::Incomplete), "{source}");
            assert_eq!(root.to_string(), source, "{source}");
            assert!(
                root.descendants().any(|node| node.kind() == recovery_kind),
                "{source}",
            );
        }
    }

    #[test]
    fn direct_operator_header_preserves_an_i8_overflow_as_one_error() {
        let source = "prefix (+) 128 =";
        let (outcome, output) = parse_recovered_operator(source);
        let root = SyntaxNode::new_root(output.finish_complete());

        assert!(matches!(outcome, Recovered::Incomplete));
        assert_eq!(root.to_string(), source);
        let errors = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].text(), "128");
    }

    #[test]
    fn direct_operator_header_missing_equals_closes_the_header() {
        let source = "prefix (+) 50";
        let (outcome, output) = parse_recovered_operator(source);
        let root = SyntaxNode::new_root(output.finish_complete());

        assert!(matches!(outcome, Recovered::Incomplete));
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
        );
        assert_eq!(root.kind(), SyntaxKind::OperatorHeader);
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
            let (header_declaration, _) = parse_direct_use_with_output(source, HeaderOutput::new());
            let (full_declaration, full_output) =
                parse_direct_use_with_output(source, FullCstOutput::new(source));
            assert_eq!(header_declaration, full_declaration, "{source}");
            assert_eq!(
                full_output.finish_complete().to_string(),
                source,
                "{source}"
            );
        }
    }

    #[test]
    fn direct_use_glob_keeps_alias_without_and_qualifier_tokens_losslessly() {
        let source = "use std::* as all as every without {foo, (*)} v1 with program::ui";
        let (declaration, output) =
            parse_direct_use_with_output(source, FullCstOutput::new(source));
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
        let [UseSegment::Operator { range, text }, UseSegment::Word(word)] =
            at_spec_start.tree().prefix().segments()
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
        assert_eq!(binding.visibility(), Visibility::Private);
        assert!(matches!(binding.target(), Recovered::Complete(pattern) if pattern.range() == (3..8)));
        assert!(matches!(binding.definition(), Some(definition)
            if matches!(definition.body(), Recovered::Complete(BindingBody::Inline { expression }) if expression.range() == (11..14))));
        assert_eq!(i.input.remainder(), "\n");
    }

    #[test]
    fn mod_declaration_keeps_named_and_test_identity_shapes_distinct() {
        let cases = [
            ("mod Foo;", false, true),
            ("mod test;", true, false),
            ("our mod test parser: my value = 1", true, true),
            ("pub mod Box { my value = 1 }", false, true),
        ];
        for (source, marker, named) in cases {
            let (declaration, remainder) = parse_mod(source);
            assert_eq!(declaration.test_marker.is_some(), marker, "{source}");
            assert_eq!(declaration.name.is_some(), named, "{source}");
            assert_eq!(remainder, "", "{source}");
        }
    }

    #[test]
    fn mod_ast_keeps_each_of_the_three_body_forms_distinct() {
        let (bodyless, _) = parse_mod("mod outer;");
        assert!(matches!(bodyless.body, Recovered::Complete(ModBody::Bodyless { .. })));

        let (braced, _) = parse_mod("mod outer { my value = 1 }");
        assert!(matches!(braced.body, Recovered::Complete(ModBody::Braced { .. })));

        let (colon, _) = parse_mod("mod outer: my value = 1");
        assert!(matches!(
            colon.body,
            Recovered::Complete(ModBody::Colon {
                colon: Recovered::Complete(_),
                body: Recovered::Complete(ModColonBody::Inline { statement }),
            }) if matches!(*statement, crate::grammar::expression::Statement::Binding(_))
        ));

        let (missing_name, _) = parse_mod("mod ;");
        assert!(matches!(missing_name.name, Some(Recovered::Incomplete)));
        assert!(matches!(missing_name.body, Recovered::Complete(ModBody::Bodyless { .. })));
    }

    #[test]
    fn mod_test_at_eof_keeps_the_mandatory_second_name_slot() {
        let (declaration, remainder) = parse_mod("mod test");
        assert!(declaration.test_marker.is_some());
        assert!(matches!(declaration.name, Some(Recovered::Incomplete)));
        assert!(matches!(declaration.body, Recovered::Incomplete));
        assert_eq!(remainder, "");
    }

    #[test]
    fn mod_and_test_are_exact_contextual_words_only() {
        assert!(!parses_mod("module outer;"));
        assert!(!parses_mod("modular outer;"));
        let (declaration, remainder) = parse_mod("mod testable;");
        assert!(declaration.test_marker.is_none());
        assert!(matches!(declaration.name, Some(Recovered::Complete(word)) if word.text() == "testable"));
        assert_eq!(remainder, "");
    }

    #[test]
    fn direct_mod_declaration_reuses_the_canonical_statement_bodies_losslessly() {
        let table = crate::operator::OperatorTable::empty();
        for (source, mods, markers) in [
            ("mod outer { my value = 1; mod test: my nested = 2 }", 2, 1),
            ("mod outer:\n  my value = 1\n  mod test;", 2, 1),
            ("my\n  mod visible;", 1, 0),
        ] {
            let output = parse_direct_root_candidate(source, &table, &[]);
            let root = SyntaxNode::new_root(output.green().clone());
            assert_eq!(root.to_string(), source, "{source}");
            assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::ModDeclaration).count(), mods, "{source}");
            assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::TestModuleMarker).count(), markers, "{source}");
        }
    }

    #[test]
    fn statement_recovery_retries_a_nested_mod_as_a_canonical_candidate() {
        let source = "mod outer:\n  @mod child;";
        let table = crate::operator::OperatorTable::empty();
        let output = parse_direct_root_candidate(source, &table, &[]);
        let root = SyntaxNode::new_root(output.green().clone());
        assert_eq!(root.to_string(), source);
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::ModDeclaration).count(), 2);
        assert_eq!(output.committed_recoveries().len(), 1);
    }

    #[test]
    fn direct_mod_missing_identity_does_not_cascade_a_body_introducer() {
        let table = crate::operator::OperatorTable::empty();
        for (source, role) in [
            ("mod", ModRole::Name),
            ("mod test", ModRole::TestName),
        ] {
            let output = parse_direct_root_candidate(source, &table, &[]);
            let records = output.committed_recoveries();
            assert_eq!(records.len(), 1, "{source}");
            assert_eq!(records[0].kind, RecoveryKind::Missing, "{source}");
            assert_eq!(records[0].site.role, GrammarRole::Declaration(DeclarationRole::Mod(role)), "{source}");
            assert_eq!(records[0].expectations[0].expected, ExpectedSyntax::Identifier, "{source}");
        }
    }

    #[test]
    fn direct_mod_complete_identity_requires_one_union_body_introducer_slot() {
        let table = crate::operator::OperatorTable::empty();
        let output = parse_direct_root_candidate("mod outer", &table, &[]);
        let [record] = output.committed_recoveries() else { panic!("one body-introducer slot expected"); };
        assert_eq!(record.site.role, GrammarRole::Declaration(DeclarationRole::Mod(ModRole::BodyIntroducer)));
        assert_eq!(record.expectations.len(), 3);
        assert_eq!(record.expectations.iter().map(|expectation| expectation.expected).collect::<Vec<_>>(), [
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Semicolon),
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(Delimiter::Brace)),
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
        ]);
    }

    #[test]
    fn direct_mod_invalid_body_introducer_retries_a_starter_or_inline_statement() {
        let table = crate::operator::OperatorTable::empty();
        for (source, bindings) in [
            ("mod outer @;", 0),
            ("mod outer @my value = 1", 1),
        ] {
            let output = parse_direct_root_candidate(source, &table, &[]);
            let root = SyntaxNode::new_root(output.green().clone());
            assert_eq!(root.to_string(), source, "{source}");
            let [record] = output.committed_recoveries() else {
                panic!("one body-introducer error expected for {source}");
            };
            assert_eq!(record.kind, RecoveryKind::Error, "{source}");
            assert_eq!(record.site.role, GrammarRole::Declaration(DeclarationRole::Mod(ModRole::BodyIntroducer)), "{source}");
            assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::BindingStatement).count(), bindings, "{source}");
        }
    }

    #[test]
    fn mod_ast_retries_malformed_introducer_and_colon_body_to_the_same_statement_slot() {
        for source in [
            "mod outer @my value = 1",
            "mod outer: @my value = 1",
        ] {
            let (declaration, remainder) = parse_mod(source);
            assert_eq!(remainder, "", "{source}");
            let Recovered::Complete(ModBody::Colon { body, .. }) = declaration.body else {
                panic!("a recovered colon body was expected for {source}");
            };
            assert!(matches!(
                body,
                Recovered::Complete(ModColonBody::Inline { statement })
                    if matches!(*statement, crate::grammar::expression::Statement::Binding(_))
            ), "{source}");
        }
    }

    #[test]
    fn mod_direct_retries_malformed_introducer_and_colon_body_under_their_own_roles() {
        let table = crate::operator::OperatorTable::empty();
        for (source, role) in [
            ("mod outer = my value = 1", ModRole::BodyIntroducer),
            ("mod outer: @my value = 1", ModRole::Body),
        ] {
            let output = parse_direct_root_candidate(source, &table, &[]);
            let root = SyntaxNode::new_root(output.green().clone());
            assert_eq!(root.to_string(), source, "{source}");
            assert_eq!(
                output.committed_recoveries().iter().filter(|record| {
                    record.kind == RecoveryKind::Error
                        && record.site.role == GrammarRole::Declaration(DeclarationRole::Mod(role))
                }).count(),
                1,
                "{source}: {:?}",
                output.committed_recoveries(),
            );
            assert!(!output.committed_recoveries().iter().any(|record| {
                record.kind == RecoveryKind::Missing
                    && record.site.role == GrammarRole::Declaration(DeclarationRole::Mod(role))
            }), "{source}: {:?}", output.committed_recoveries());
        }
    }

    #[test]
    fn mod_identity_recovery_leaves_brace_statement_boundaries_to_the_outer_owner() {
        let table = crate::operator::OperatorTable::empty();
        for source in [
            "mod outer { mod inner, next }",
            "mod outer { mod inner\nnext }",
            "mod outer { mod inner }",
        ] {
            let output = parse_direct_root_candidate(source, &table, &[]);
            let root = SyntaxNode::new_root(output.green().clone());
            assert_eq!(root.to_string(), source, "{source}");
            let body_records = output.committed_recoveries().iter().filter(|record| {
                record.site.role == GrammarRole::Declaration(DeclarationRole::Mod(ModRole::BodyIntroducer))
            }).count();
            assert_eq!(body_records, 1, "{source}");
            assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::ModDeclaration).count(), 2, "{source}");
        }
    }

    #[test]
    fn mod_colon_body_missing_keeps_outer_comma_and_close_available() {
        let table = crate::operator::OperatorTable::empty();
        for source in [
            "mod outer:",
            "mod outer { mod inner:, next }",
            "mod outer { mod inner: }",
        ] {
            let output = parse_direct_root_candidate(source, &table, &[]);
            let root = SyntaxNode::new_root(output.green().clone());
            assert_eq!(root.to_string(), source, "{source}");
            assert_eq!(
                output.committed_recoveries().iter().filter(|record| {
                    record.kind == RecoveryKind::Missing
                        && record.site.role == GrammarRole::Declaration(DeclarationRole::Mod(ModRole::Body))
                }).count(),
                1,
                "{source}: {:?}",
                output.committed_recoveries(),
            );
        }
    }

    #[test]
    fn mod_brace_body_reuses_the_shared_owner_safe_close_recovery() {
        let table = crate::operator::OperatorTable::empty();
        for (source, kind, range) in [
            ("mod outer { item", RecoveryKind::Missing, 16..16),
            ("mod outer { item ]", RecoveryKind::Error, 17..18),
        ] {
            let output = parse_direct_root_candidate(source, &table, &[]);
            let root = SyntaxNode::new_root(output.green().clone());
            assert_eq!(root.to_string(), source, "{source}");
            assert!(output.committed_recoveries().iter().any(|record| {
                record.kind == kind
                    && record.site.range == range
                    && record.site.role == GrammarRole::ClosingDelimiter {
                        owner: ConstructRole::BracedStatementBlockExpression,
                        delimiter: Delimiter::Brace,
                    }
            }), "{source}: {:?}", output.committed_recoveries());
        }
    }

    #[test]
    fn direct_mod_indented_body_keeps_its_statement_recovery_under_mod_owner() {
        let table = crate::operator::OperatorTable::empty();
        let output = parse_direct_root_candidate("mod outer:\n  ", &table, &[]);
        let [record] = output.committed_recoveries() else { panic!("one indented statement slot expected"); };
        assert_eq!(record.kind, RecoveryKind::Missing);
        assert_eq!(record.site.role, GrammarRole::Declaration(DeclarationRole::Mod(ModRole::IndentedStatement)));
        assert_eq!(record.expectations[0].expected, ExpectedSyntax::Statement);
    }

    #[test]
    fn direct_mod_missing_colon_retries_a_canonical_statement() {
        let source = "mod outer my value = 1";
        let table = crate::operator::OperatorTable::empty();
        let output = parse_direct_root_candidate(source, &table, &[]);
        let root = SyntaxNode::new_root(output.green().clone());
        assert_eq!(root.to_string(), source);
        let [record] = output.committed_recoveries() else {
            panic!("one recovered body introducer expected");
        };
        assert_eq!(record.kind, RecoveryKind::Missing);
        assert_eq!(record.site.role, GrammarRole::Declaration(DeclarationRole::Mod(ModRole::BodyIntroducer)));
        assert_eq!(record.expectations[0].expected, ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon));
        assert!(root.descendants().any(|node| node.kind() == SyntaxKind::BindingStatement));
    }

    #[test]
    fn direct_mod_missing_colon_can_retry_a_nested_mod_statement() {
        let source = "mod outer mod child;";
        let table = crate::operator::OperatorTable::empty();
        let output = parse_direct_root_candidate(source, &table, &[]);
        let root = SyntaxNode::new_root(output.green().clone());
        assert_eq!(root.to_string(), source);
        let [record] = output.committed_recoveries() else {
            panic!("one recovered body introducer expected");
        };
        assert_eq!(record.kind, RecoveryKind::Missing);
        assert_eq!(record.site.role, GrammarRole::Declaration(DeclarationRole::Mod(ModRole::BodyIntroducer)));
        assert_eq!(record.expectations[0].expected, ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon));
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::ModDeclaration).count(), 2);
    }

    #[test]
    fn direct_mod_invalid_name_retries_a_later_raw_name_locally() {
        let source = "mod @outer;";
        let table = crate::operator::OperatorTable::empty();
        let output = parse_direct_root_candidate(source, &table, &[]);
        let root = SyntaxNode::new_root(output.green().clone());
        assert_eq!(root.to_string(), source);
        let [record] = output.committed_recoveries() else { panic!("one name error expected"); };
        assert_eq!(record.kind, RecoveryKind::Error);
        assert_eq!(record.site.role, GrammarRole::Declaration(DeclarationRole::Mod(ModRole::Name)));
        assert_eq!(record.site.range, 4..5);
        assert!(root.to_string().contains("outer"));
    }

    #[test]
    fn direct_mod_test_name_error_retries_without_losing_the_marker() {
        let source = "mod test @outer;";
        let table = crate::operator::OperatorTable::empty();
        let output = parse_direct_root_candidate(source, &table, &[]);
        let root = SyntaxNode::new_root(output.green().clone());
        assert_eq!(root.to_string(), source);
        let [record] = output.committed_recoveries() else { panic!("one test-name error expected"); };
        assert_eq!(record.kind, RecoveryKind::Error);
        assert_eq!(record.site.role, GrammarRole::Declaration(DeclarationRole::Mod(ModRole::TestName)));
        assert_eq!(record.site.range, 9..10);
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::TestModuleMarker).count(), 1);
    }

    #[test]
    fn visibility_prefixed_mod_keeps_authority_over_a_binding_target_named_mod() {
        let (declaration, remainder) = parse_mod("my mod = value");
        assert_eq!(remainder, "= value");
        assert!(matches!(declaration.name, Some(Recovered::Incomplete)));

        let table = crate::operator::OperatorTable::empty();
        let output = parse_direct_root_candidate("my mod = value", &table, &[]);
        let root = SyntaxNode::new_root(output.green().clone());
        assert!(root.descendants().any(|node| node.kind() == SyntaxKind::ModDeclaration));
        assert!(!root.descendants().any(|node| node.kind() == SyntaxKind::BindingStatement));
    }

    #[test]
    fn type_intro_judge_recognizes_exact_keyword_with_optional_visibility() {
        for (source, expected_visibility, visibility_range, trivia_range, keyword_range, remainder) in [
            ("type", None, None, None, 0..4, ""),
            ("type = Missing", None, None, None, 0..4, " = Missing"),
            ("my type", Some(Visibility::Private), Some(0..2), Some(2..3), 3..7, ""),
            ("our type", Some(Visibility::Our), Some(0..3), Some(3..4), 4..8, ""),
            ("pub type", Some(Visibility::Public), Some(0..3), Some(3..4), 4..8, ""),
            ("my\n  type", Some(Visibility::Private), Some(0..2), Some(2..5), 5..9, ""),
        ] {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            let mut expectations = chasa::LatestSink::new();
            let mut is_cut = false;
            let intro = {
                let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
                    .set_local(&mut local);
                i.run(recognize_type_statement_intro)
                    .expect("exact Type declaration introduction")
            };

            assert_eq!(intro.start, 0, "{source:?}");
            assert_eq!(intro.type_base, 0, "{source:?}");
            assert_eq!(intro.type_keyword.range(), keyword_range, "{source:?}");
            assert_eq!(
                intro.visibility.as_ref().map(|visibility| visibility.visibility),
                expected_visibility,
                "{source:?}"
            );
            assert_eq!(
                intro.visibility.as_ref().map(|visibility| visibility.keyword.range()),
                visibility_range,
                "{source:?}"
            );
            assert_eq!(
                intro.after_visibility.as_ref().map(TriviaRun::range),
                trivia_range,
                "{source:?}"
            );
            assert_eq!(source_input.remainder(), remainder, "{source:?}");
        }
    }

    #[test]
    fn type_intro_judge_rejects_non_type_without_state_or_input_changes() {
        for source in ["my x = 1", "structure", "my\ntype", "pub type_name"] {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            let line_before = local.line();
            let mut expectations = chasa::LatestSink::new();
            let mut is_cut = false;
            let intro = {
                let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
                    .set_local(&mut local);
                i.run(recognize_type_statement_intro)
            };

            assert!(intro.is_none(), "{source:?}");
            assert_eq!(source_input.remainder(), source, "{source:?}");
            assert_eq!(local.line(), line_before, "{source:?}");
            assert!(!is_cut, "{source:?}");
        }
    }

    #[test]
    fn declaration_type_parameter_list_is_optional_same_line_and_lossless() {
        fn scan_after_type_name<'source>(
            source: &'source str,
        ) -> (Option<Vec<DeclarationTypeParameter<'source>>>, String) {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            let mut expectations = chasa::LatestSink::new();
            let mut is_cut = false;
            let parameters = {
                let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
                    .set_local(&mut local);
                assert!(matches!(i.run(scan_word), Some(word) if word.text() == "type"));
                assert!(i.run(scan_trivia).is_some());
                assert!(matches!(i.run(scan_word), Some(word) if word.text() == "Name"));
                scan_declaration_type_parameter_list(&mut i)
            };
            (parameters, source_input.remainder().to_owned())
        }

        let (parameters, remainder) = scan_after_type_name("type Name = Int");
        assert!(parameters.is_none());
        assert_eq!(remainder, " = Int");

        let (parameters, remainder) = scan_after_type_name("type Name 'a = Int");
        assert!(matches!(
            parameters.as_deref(),
            Some([DeclarationTypeParameter::SigilIdentifier(word)]) if word.text() == "'a"
        ));
        assert_eq!(remainder, " = Int");

        let (parameters, remainder) = scan_after_type_name("type Name 'left 'right = Int");
        assert!(matches!(
            parameters.as_deref(),
            Some([
                DeclarationTypeParameter::SigilIdentifier(left),
                DeclarationTypeParameter::SigilIdentifier(right),
            ]) if left.text() == "'left" && right.text() == "'right"
        ));
        assert_eq!(remainder, " = Int");

        let (parameters, remainder) = scan_after_type_name("type Name $a &a 'a _a = Int");
        assert!(matches!(
            parameters.as_deref(),
            Some([
                DeclarationTypeParameter::SigilIdentifier(dollar),
                DeclarationTypeParameter::SigilIdentifier(ampersand),
                DeclarationTypeParameter::SigilIdentifier(apostrophe),
                DeclarationTypeParameter::Identifier(underscore),
            ]) if dollar.text() == "$a"
                && ampersand.text() == "&a"
                && apostrophe.text() == "'a"
                && underscore.text() == "_a"
        ));
        assert_eq!(remainder, " = Int");

        let (parameters, remainder) = scan_after_type_name("type Name 'a with = Int");
        assert!(matches!(
            parameters.as_deref(),
            Some([DeclarationTypeParameter::SigilIdentifier(word)]) if word.text() == "'a"
        ));
        assert_eq!(remainder, " with = Int");

        let (parameters, remainder) = scan_after_type_name("type Name 'a\n  'b = Int");
        assert!(matches!(
            parameters.as_deref(),
            Some([DeclarationTypeParameter::SigilIdentifier(word)]) if word.text() == "'a"
        ));
        assert_eq!(remainder, "\n  'b = Int");
    }

    #[test]
    fn type_declaration_header_slots_follow_td_r_name_and_equals_recovery() {
        fn parse_ast<'source>(
            source: &'source str,
        ) -> (
            ParsedTypeDeclarationHeader<'source>,
            Vec<TypeDeclarationHeaderRecovery>,
            String,
        ) {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            let mut expectations = chasa::LatestSink::new();
            let mut is_cut = false;
            let (header, recoveries) = {
                let mut i = In::new(
                    &mut source_input,
                    &mut expectations,
                    IsCut::new(&mut is_cut),
                )
                .set_local(&mut local);
                let intro = i
                    .run(recognize_type_statement_intro)
                    .expect("Type introduction is recognized in the isolated header harness");
                parse_type_declaration_header_slots(&intro, &mut i)
            };
            (header, recoveries, source_input.remainder().to_owned())
        }

        fn parse_direct<'source>(
            source: &'source str,
        ) -> (ParsedTypeDeclarationHeader<'source>, HeaderOutput, String) {
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
                .run(recognize_type_statement_intro)
                .expect("Type introduction is recognized in the isolated direct harness");
            let mut committed = probe.commit(HeaderOutput::new());
            let header = commit_type_declaration_header_slots(&intro, &mut committed);
            let remainder = committed.probe(|probe| probe.input().input.remainder().to_owned());
            (header, committed.into_output(), remainder)
        }

        let cases = [
            (
                "type",
                None,
                0,
                Recovered::Incomplete,
                false,
                "",
                vec![(RecoveryKind::Missing, TypeDeclarationRole::Name, 4..4)],
            ),
            (
                "type = Int",
                None,
                0,
                Recovered::Complete(5..6),
                true,
                " Int",
                vec![(RecoveryKind::Missing, TypeDeclarationRole::Name, 5..5)],
            ),
            (
                "type @Name = Int",
                Some(("Name", 6..10)),
                0,
                Recovered::Complete(11..12),
                true,
                " Int",
                vec![(RecoveryKind::Error, TypeDeclarationRole::Name, 5..6)],
            ),
            (
                "type @= Int",
                None,
                0,
                Recovered::Complete(6..7),
                true,
                " Int",
                vec![(RecoveryKind::Error, TypeDeclarationRole::Name, 5..6)],
            ),
            (
                "type Id = Int",
                Some(("Id", 5..7)),
                0,
                Recovered::Complete(8..9),
                true,
                " Int",
                vec![],
            ),
            (
                "type Id 'a 'b = Int",
                Some(("Id", 5..7)),
                2,
                Recovered::Complete(14..15),
                true,
                " Int",
                vec![],
            ),
            (
                "type Id 'a @= Int",
                Some(("Id", 5..7)),
                1,
                Recovered::Complete(12..13),
                true,
                " Int",
                vec![(
                    RecoveryKind::Error,
                    TypeDeclarationRole::DefinitionIntroducer,
                    11..12,
                )],
            ),
            (
                "type Id ('a)",
                Some(("Id", 5..7)),
                0,
                Recovered::Incomplete,
                true,
                "('a)",
                vec![(
                    RecoveryKind::Missing,
                    TypeDeclarationRole::DefinitionIntroducer,
                    8..8,
                )],
            ),
            (
                "type Id @('a)",
                Some(("Id", 5..7)),
                0,
                Recovered::Incomplete,
                true,
                "('a)",
                vec![(
                    RecoveryKind::Error,
                    TypeDeclarationRole::DefinitionIntroducer,
                    8..9,
                )],
            ),
            (
                "type Id",
                Some(("Id", 5..7)),
                0,
                Recovered::Incomplete,
                false,
                "",
                vec![(
                    RecoveryKind::Missing,
                    TypeDeclarationRole::DefinitionIntroducer,
                    7..7,
                )],
            ),
            (
                "type Id;",
                Some(("Id", 5..7)),
                0,
                Recovered::Incomplete,
                false,
                ";",
                vec![(
                    RecoveryKind::Missing,
                    TypeDeclarationRole::DefinitionIntroducer,
                    7..7,
                )],
            ),
            (
                "type Id\nInt",
                Some(("Id", 5..7)),
                0,
                Recovered::Incomplete,
                false,
                "\nInt",
                vec![(
                    RecoveryKind::Missing,
                    TypeDeclarationRole::DefinitionIntroducer,
                    7..7,
                )],
            ),
            (
                "type Id @",
                Some(("Id", 5..7)),
                0,
                Recovered::Incomplete,
                false,
                "",
                vec![(
                    RecoveryKind::Error,
                    TypeDeclarationRole::DefinitionIntroducer,
                    8..9,
                )],
            ),
        ];

        for (source, expected_name, parameter_count, expected_equals, rhs_retry, remainder, expected_records) in cases {
            let (ast, ast_recoveries, ast_remainder) = parse_ast(source);
            let (direct, output, direct_remainder) = parse_direct(source);

            assert_eq!(ast, direct, "AST/direct header slots diverged for {source:?}");
            match (&ast.name, expected_name) {
                (Recovered::Incomplete, None) => {}
                (Recovered::Complete(actual), Some((text, range))) => {
                    assert_eq!(actual.text(), text, "{source:?}");
                    assert_eq!(actual.range(), range, "{source:?}");
                }
                _ => panic!("unexpected declaration name recovery for {source:?}: {:?}", ast.name),
            }
            assert_eq!(ast.parameters.len(), parameter_count, "{source:?}");
            assert_eq!(ast.equals, expected_equals, "{source:?}");
            assert_eq!(ast.rhs_retry, rhs_retry, "{source:?}");
            assert_eq!(ast_remainder, remainder, "{source:?}");
            assert_eq!(direct_remainder, remainder, "{source:?}");

            let direct_records = output
                .committed_recoveries()
                .iter()
                .map(|record| {
                    let GrammarRole::Declaration(DeclarationRole::Type(role)) = record.site.role else {
                        panic!("unexpected recovery role for {source:?}: {:?}", record.site.role);
                    };
                    (record.kind, role, record.site.range.clone())
                })
                .collect::<Vec<_>>();
            assert_eq!(direct_records, expected_records, "{source:?}");
            assert_eq!(ast_recoveries.len(), expected_records.len(), "{source:?}");
            for (recovery, (kind, role, range)) in ast_recoveries.iter().zip(&expected_records) {
                match recovery {
                    TypeDeclarationHeaderRecovery::Missing { role: actual, at } => {
                        assert_eq!(*kind, RecoveryKind::Missing, "{source:?}");
                        assert_eq!(actual, role, "{source:?}");
                        assert_eq!((*at)..(*at), range.clone(), "{source:?}");
                    }
                    TypeDeclarationHeaderRecovery::Error { role: actual, range: actual_range } => {
                        assert_eq!(*kind, RecoveryKind::Error, "{source:?}");
                        assert_eq!(actual, role, "{source:?}");
                        assert_eq!(actual_range, range, "{source:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn declaration_exact_equals_scanner_accepts_only_the_lone_operator_run() {
        for (source, accepted, remainder) in [
            ("= Int", Some(0..1), " Int"),
            ("== Int", None, "== Int"),
            ("=> Int", None, "=> Int"),
            ("=+ Int", None, "=+ Int"),
        ] {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            let mut expectations = chasa::LatestSink::new();
            let mut is_cut = false;
            let result = {
                let mut i = In::new(
                    &mut source_input,
                    &mut expectations,
                    IsCut::new(&mut is_cut),
                )
                .set_local(&mut local);
                i.run(scan_declaration_exact_equals)
            };
            assert_eq!(result, accepted, "{source:?}");
            assert_eq!(source_input.remainder(), remainder, "{source:?}");
        }
    }

    #[test]
    fn type_declaration_definition_introducer_leaves_a_live_outer_else_gap_unconsumed() {
        const IF_WORDS: &[&str] = &["elsif", "else"];
        let source = "type Id else: 0";

        let mut ast_source = SourceInput::new(source);
        let mut ast_local = ParseLocal::new();
        let root_scope = ast_local.push_root_statement_ambient_scope();
        let companion = ast_local.push_if_expression_companion(0, IF_WORDS);
        let mut ast_expectations = chasa::LatestSink::new();
        let mut ast_cut = false;
        let (ast_header, ast_recoveries) = {
            let mut i = In::new(
                &mut ast_source,
                &mut ast_expectations,
                IsCut::new(&mut ast_cut),
            )
            .set_local(&mut ast_local);
            let intro = i
                .run(recognize_type_statement_intro)
                .expect("Type introduction is recognized");
            parse_type_declaration_header_slots(&intro, &mut i)
        };
        assert_eq!(ast_source.remainder(), " else: 0");
        assert!(matches!(ast_header.name, Recovered::Complete(word) if word.text() == "Id"));
        assert!(matches!(ast_header.equals, Recovered::Incomplete));
        assert!(!ast_header.rhs_retry);
        assert_eq!(
            ast_recoveries,
            vec![TypeDeclarationHeaderRecovery::Missing {
                role: TypeDeclarationRole::DefinitionIntroducer,
                at: 7,
            }]
        );
        assert_eq!(
            ast_local.pop_if_expression_companion().map(|frame| frame.id()),
            Some(companion)
        );
        assert_eq!(ast_local.pop_ambient_owner_scope(), Some(root_scope));

        let mut direct_source = SourceInput::new(source);
        let mut direct_local = ParseLocal::new();
        let root_scope = direct_local.push_root_statement_ambient_scope();
        let companion = direct_local.push_if_expression_companion(0, IF_WORDS);
        let mut direct_expectations = chasa::LatestSink::new();
        let mut direct_cut = false;
        let i = In::new(
            &mut direct_source,
            &mut direct_expectations,
            IsCut::new(&mut direct_cut),
        )
        .set_local(&mut direct_local);
        let mut probe = Probe::new(i);
        let intro = probe
            .input()
            .run(recognize_type_statement_intro)
            .expect("Type introduction is recognized");
        let mut committed = probe.commit(HeaderOutput::new());
        let direct_header = commit_type_declaration_header_slots(&intro, &mut committed);
        assert_eq!(
            committed.probe(|probe| probe.input().input.remainder()),
            " else: 0"
        );
        assert_eq!(direct_header, ast_header);
        let output = committed.into_output();
        let [record] = output.committed_recoveries() else {
            panic!("one DefinitionIntroducer Missing record expected");
        };
        assert_eq!(record.kind, RecoveryKind::Missing);
        assert_eq!(
            record.site.role,
            GrammarRole::Declaration(DeclarationRole::Type(
                TypeDeclarationRole::DefinitionIntroducer,
            ))
        );
        assert_eq!(record.site.range, 7..7);
        assert_eq!(
            direct_local.pop_if_expression_companion().map(|frame| frame.id()),
            Some(companion)
        );
        assert_eq!(direct_local.pop_ambient_owner_scope(), Some(root_scope));
    }

    #[test]
    fn type_declaration_rhs_wiring_is_atomic_typed_and_state_balanced() {
        const IF_WORDS: &[&str] = &["elsif", "else"];
        let outer_baseline = IndentationBaseline {
            column: 0,
            kind: IndentationBaselineKind::Block,
        };
        let outer_stops = StopSet::default().with(StopKind::RightBracket);

        fn parse_ast<'source>(
            source: &'source str,
            ambient: bool,
            outer_baseline: IndentationBaseline,
            outer_stops: StopSet,
        ) -> (Recovered<Box<TypeExpression<'source>>>, String) {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            local.push_indentation_baseline(outer_baseline);
            local.push_stop_set(outer_stops);
            let ambient_scope = ambient.then(|| local.push_root_statement_ambient_scope());
            let companion = ambient.then(|| local.push_if_expression_companion(0, IF_WORDS));
            let mut expectations = chasa::LatestSink::new();
            let mut is_cut = false;
            let rhs = {
                let mut i = In::new(
                    &mut source_input,
                    &mut expectations,
                    IsCut::new(&mut is_cut),
                )
                .set_local(&mut local);
                let intro = i
                    .run(recognize_type_statement_intro)
                    .expect("Type introduction is recognized in the isolated RHS harness");
                let (header, _) = parse_type_declaration_header_slots(&intro, &mut i);
                parse_type_declaration_rhs(&header, intro.type_base, &mut i)
            };
            assert_eq!(local.indentation_baseline(), Some(outer_baseline), "{source:?}");
            assert_eq!(local.stop_set(), Some(outer_stops), "{source:?}");
            if let Some(companion) = companion {
                assert_eq!(
                    local.pop_if_expression_companion().map(|frame| frame.id()),
                    Some(companion),
                    "{source:?}"
                );
            }
            if let Some(ambient_scope) = ambient_scope {
                assert_eq!(local.pop_ambient_owner_scope(), Some(ambient_scope), "{source:?}");
            }
            assert_eq!(local.pop_stop_set(), Some(outer_stops), "{source:?}");
            assert_eq!(
                local.pop_indentation_baseline(),
                Some(outer_baseline),
                "{source:?}"
            );
            (rhs, source_input.remainder().to_owned())
        }

        fn parse_direct<'source>(
            source: &'source str,
            ambient: bool,
            outer_baseline: IndentationBaseline,
            outer_stops: StopSet,
        ) -> (Recovered<Range<usize>>, HeaderOutput, String) {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            local.push_indentation_baseline(outer_baseline);
            local.push_stop_set(outer_stops);
            let ambient_scope = ambient.then(|| local.push_root_statement_ambient_scope());
            let companion = ambient.then(|| local.push_if_expression_companion(0, IF_WORDS));
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
                .run(recognize_type_statement_intro)
                .expect("Type introduction is recognized in the isolated direct RHS harness");
            let mut committed = probe.commit(HeaderOutput::new());
            let header = commit_type_declaration_header_slots(&intro, &mut committed);
            let rhs = commit_type_declaration_rhs(&header, intro.type_base, &mut committed);
            let remainder = committed.probe(|probe| probe.input().input.remainder().to_owned());
            let output = committed.into_output();

            assert_eq!(local.indentation_baseline(), Some(outer_baseline), "{source:?}");
            assert_eq!(local.stop_set(), Some(outer_stops), "{source:?}");
            if let Some(companion) = companion {
                assert_eq!(
                    local.pop_if_expression_companion().map(|frame| frame.id()),
                    Some(companion),
                    "{source:?}"
                );
            }
            if let Some(ambient_scope) = ambient_scope {
                assert_eq!(local.pop_ambient_owner_scope(), Some(ambient_scope), "{source:?}");
            }
            assert_eq!(local.pop_stop_set(), Some(outer_stops), "{source:?}");
            assert_eq!(
                local.pop_indentation_baseline(),
                Some(outer_baseline),
                "{source:?}"
            );
            (rhs, output, remainder)
        }

        let cases = [
            (
                "type",
                false,
                None,
                "",
                vec![(
                    RecoveryKind::Missing,
                    GrammarRole::Declaration(DeclarationRole::Type(
                        TypeDeclarationRole::Name,
                    )),
                    4..4,
                )],
            ),
            (
                "type = Int",
                false,
                Some(7..10),
                "",
                vec![(
                    RecoveryKind::Missing,
                    GrammarRole::Declaration(DeclarationRole::Type(
                        TypeDeclarationRole::Name,
                    )),
                    5..5,
                )],
            ),
            ("type Id = Int", false, Some(10..13), "", vec![]),
            ("type Id = [e] T", false, Some(10..15), "", vec![]),
            (
                "type Id ('a)",
                false,
                Some(8..12),
                "",
                vec![(
                    RecoveryKind::Missing,
                    GrammarRole::Declaration(DeclarationRole::Type(
                        TypeDeclarationRole::DefinitionIntroducer,
                    )),
                    8..8,
                )],
            ),
            (
                "type Id =",
                false,
                None,
                "",
                vec![(
                    RecoveryKind::Missing,
                    type_declaration_rhs_role(),
                    9..9,
                )],
            ),
            (
                "type Id =;",
                false,
                None,
                ";",
                vec![(
                    RecoveryKind::Missing,
                    type_declaration_rhs_role(),
                    9..9,
                )],
            ),
            (
                "type Id = @Int",
                false,
                Some(11..14),
                "",
                vec![(
                    RecoveryKind::Error,
                    GrammarRole::Type(crate::session::TypeRole::Primary),
                    10..11,
                )],
            ),
            (
                "type Id = @;",
                false,
                None,
                ";",
                vec![(
                    RecoveryKind::Error,
                    GrammarRole::Type(crate::session::TypeRole::Primary),
                    10..11,
                )],
            ),
            (
                "type Id = else: 0",
                true,
                None,
                " else: 0",
                vec![(
                    RecoveryKind::Missing,
                    type_declaration_rhs_role(),
                    9..9,
                )],
            ),
            (
                "type Id = with tail",
                false,
                None,
                "with tail",
                vec![(
                    RecoveryKind::Missing,
                    type_declaration_rhs_role(),
                    10..10,
                )],
            ),
            ("type Id =\n  [e] T", false, Some(12..17), "", vec![]),
            (
                "type Id =\nInt",
                false,
                None,
                "\nInt",
                vec![(
                    RecoveryKind::Missing,
                    type_declaration_rhs_role(),
                    9..9,
                )],
            ),
        ];

        for (source, ambient, expected_range, expected_remainder, expected_records) in cases {
            let (ast_rhs, ast_remainder) =
                parse_ast(source, ambient, outer_baseline, outer_stops);
            let (direct_rhs, output, direct_remainder) =
                parse_direct(source, ambient, outer_baseline, outer_stops);
            let ast_range = match &ast_rhs {
                Recovered::Complete(rhs) => Some(rhs.range()),
                Recovered::Incomplete => None,
            };
            let direct_range = match direct_rhs {
                Recovered::Complete(range) => Some(range),
                Recovered::Incomplete => None,
            };
            assert_eq!(ast_range, expected_range, "{source:?}");
            assert_eq!(direct_range, expected_range, "{source:?}");
            assert_eq!(ast_remainder, expected_remainder, "{source:?}");
            assert_eq!(direct_remainder, expected_remainder, "{source:?}");
            if source == "type Id = [e] T" {
                assert!(
                    format!("{ast_rhs:?}").contains("leading_effect_row: Some"),
                    "the full BracketRow surface must remain available to Type declarations"
                );
            }

            let actual_records = output
                .committed_recoveries()
                .iter()
                .map(|record| (record.kind, record.site.role, record.site.range.clone()))
                .collect::<Vec<_>>();
            assert_eq!(actual_records, expected_records, "{source:?}");
        }
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum TypeDeclarationRhsBoundaryOwner {
        None,
        NestedIf,
        StrictIndentedDedent,
    }

    fn install_type_declaration_rhs_boundary_owner(
        local: &mut ParseLocal,
        owner: TypeDeclarationRhsBoundaryOwner,
    ) -> (Vec<AmbientOwnerScopeFrame>, Vec<IfExpressionCompanionId>) {
        let mut scopes = Vec::new();
        let mut companions = Vec::new();
        match owner {
            TypeDeclarationRhsBoundaryOwner::None => {}
            TypeDeclarationRhsBoundaryOwner::NestedIf => {
                scopes.push(local.push_root_statement_ambient_scope());
                scopes.push(local.push_indented_statement_ambient_scope(2));
                companions.push(local.push_if_expression_companion(0, &["elsif", "else"]));
                companions.push(local.push_if_expression_companion(0, &["elsif", "else"]));
            }
            TypeDeclarationRhsBoundaryOwner::StrictIndentedDedent => {
                scopes.push(local.push_root_statement_ambient_scope());
                scopes.push(local.push_indented_statement_ambient_scope(2));
            }
        }
        (scopes, companions)
    }

    fn restore_type_declaration_rhs_boundary_owner(
        local: &mut ParseLocal,
        mut scopes: Vec<AmbientOwnerScopeFrame>,
        mut companions: Vec<IfExpressionCompanionId>,
    ) {
        while let Some(expected) = companions.pop() {
            assert_eq!(
                local.pop_if_expression_companion().map(|frame| frame.id()),
                Some(expected),
            );
        }
        while let Some(expected) = scopes.pop() {
            assert_eq!(local.pop_ambient_owner_scope(), Some(expected));
        }
    }

    fn parse_type_declaration_rhs_boundary_ast<'source>(
        source: &'source str,
        type_base: usize,
        outer_stop: StopKind,
        owner: TypeDeclarationRhsBoundaryOwner,
    ) -> (Recovered<Box<TypeExpression<'source>>>, String) {
        let outer_baseline = IndentationBaseline {
            column: type_base,
            kind: IndentationBaselineKind::Block,
        };
        let outer_stops = StopSet::default().with(outer_stop);
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_indentation_baseline(outer_baseline);
        local.push_stop_set(outer_stops);
        let (scopes, companions) = install_type_declaration_rhs_boundary_owner(&mut local, owner);
        let innermost = companions.last().copied();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let rhs = {
            let mut i = In::new(
                &mut source_input,
                &mut expectations,
                IsCut::new(&mut is_cut),
            )
            .set_local(&mut local);
            let intro = i
                .run(recognize_type_statement_intro)
                .expect("Type introduction is recognized in the boundary harness");
            let (header, _) = parse_type_declaration_header_slots(&intro, &mut i);
            if let Some(innermost) = innermost && any_ambient_owner_claims(&mut i) {
                assert_eq!(if_continuation_owner(&mut i), Some(innermost), "{source:?}");
            }
            parse_type_declaration_rhs(&header, intro.type_base, &mut i)
        };
        assert_eq!(local.indentation_baseline(), Some(outer_baseline), "{source:?}");
        assert_eq!(local.stop_set(), Some(outer_stops), "{source:?}");
        restore_type_declaration_rhs_boundary_owner(&mut local, scopes, companions);
        assert_eq!(local.pop_stop_set(), Some(outer_stops), "{source:?}");
        assert_eq!(
            local.pop_indentation_baseline(),
            Some(outer_baseline),
            "{source:?}"
        );
        (rhs, source_input.remainder().to_owned())
    }

    fn parse_type_declaration_rhs_boundary_direct<'source>(
        source: &'source str,
        type_base: usize,
        outer_stop: StopKind,
        owner: TypeDeclarationRhsBoundaryOwner,
    ) -> (
        Recovered<Range<usize>>,
        Vec<(RecoveryKind, GrammarRole, Range<usize>)>,
        String,
    ) {
        let outer_baseline = IndentationBaseline {
            column: type_base,
            kind: IndentationBaselineKind::Block,
        };
        let outer_stops = StopSet::default().with(outer_stop);
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_indentation_baseline(outer_baseline);
        local.push_stop_set(outer_stops);
        let (scopes, companions) = install_type_declaration_rhs_boundary_owner(&mut local, owner);
        let innermost = companions.last().copied();
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
            .run(recognize_type_statement_intro)
            .expect("Type introduction is recognized in the direct boundary harness");
        let mut committed = probe.commit(HeaderOutput::new());
        let header = commit_type_declaration_header_slots(&intro, &mut committed);
        if let Some(innermost) = innermost
            && committed.probe(|probe| any_ambient_owner_claims(probe.input()))
        {
            assert_eq!(
                committed.probe(|probe| if_continuation_owner(probe.input())),
                Some(innermost),
                "{source:?}"
            );
        }
        let rhs = commit_type_declaration_rhs(&header, intro.type_base, &mut committed);
        let remainder = committed.probe(|probe| probe.input().input.remainder().to_owned());
        let output = committed.into_output();
        let records = output
            .committed_recoveries()
            .iter()
            .map(|record| (record.kind, record.site.role, record.site.range.clone()))
            .collect();

        assert_eq!(local.indentation_baseline(), Some(outer_baseline), "{source:?}");
        assert_eq!(local.stop_set(), Some(outer_stops), "{source:?}");
        restore_type_declaration_rhs_boundary_owner(&mut local, scopes, companions);
        assert_eq!(local.pop_stop_set(), Some(outer_stops), "{source:?}");
        assert_eq!(
            local.pop_indentation_baseline(),
            Some(outer_baseline),
            "{source:?}"
        );
        (rhs, records, remainder)
    }

    #[test]
    fn type_declaration_rhs_boundary_parity_exhausts_outer_owner_gaps() {
        let rhs_role = type_declaration_rhs_role();
        let missing_rhs = |at| vec![(RecoveryKind::Missing, rhs_role, at..at)];

        // These distinguish Type's two added stops from already-active outer
        // stops; all must remain live again after the nested RHS scope exits.
        for (source, outer_stop, remainder, at) in [
            ("type Id =", StopKind::Semicolon, "", 9),
            ("type Id =", StopKind::With, "", 9),
            ("type Id =", StopKind::Arrow, "", 9),
            ("type Id =", StopKind::RightBrace, "", 9),
            ("type Id =; tail", StopKind::Semicolon, "; tail", 9),
            ("type Id = with Tail", StopKind::With, "with Tail", 10),
            ("type Id = -> Tail", StopKind::Arrow, "-> Tail", 10),
            ("type Id = }", StopKind::RightBrace, "}", 10),
        ] {
            let (ast_rhs, ast_remainder) = parse_type_declaration_rhs_boundary_ast(
                source,
                0,
                outer_stop,
                TypeDeclarationRhsBoundaryOwner::None,
            );
            let (direct_rhs, records, direct_remainder) = parse_type_declaration_rhs_boundary_direct(
                source,
                0,
                outer_stop,
                TypeDeclarationRhsBoundaryOwner::None,
            );
            assert!(matches!(ast_rhs, Recovered::Incomplete), "AST {source:?}");
            assert!(matches!(direct_rhs, Recovered::Incomplete), "direct {source:?}");
            assert_eq!(ast_remainder, remainder, "AST {source:?}");
            assert_eq!(direct_remainder, remainder, "direct {source:?}");
            assert_eq!(records, missing_rhs(at), "direct {source:?}");
        }

        // An inner If frame owns both companion spellings, while a visible
        // indented statement owner independently claims its strict dedent.
        for source in ["type Id = else: 0", "type Id = elsif: 0"] {
            let (ast_rhs, ast_remainder) = parse_type_declaration_rhs_boundary_ast(
                source,
                0,
                StopKind::RightBracket,
                TypeDeclarationRhsBoundaryOwner::NestedIf,
            );
            let (direct_rhs, records, direct_remainder) = parse_type_declaration_rhs_boundary_direct(
                source,
                0,
                StopKind::RightBracket,
                TypeDeclarationRhsBoundaryOwner::NestedIf,
            );
            assert!(matches!(ast_rhs, Recovered::Incomplete), "AST {source:?}");
            assert!(matches!(direct_rhs, Recovered::Incomplete), "direct {source:?}");
            assert_eq!(ast_remainder, &source[9..], "AST {source:?}");
            assert_eq!(direct_remainder, &source[9..], "direct {source:?}");
            assert_eq!(records, missing_rhs(9), "direct {source:?}");
        }
        let source = "type Id =\nelse: 0";
        let (ast_rhs, ast_remainder) = parse_type_declaration_rhs_boundary_ast(
            source,
            0,
            StopKind::RightBracket,
            TypeDeclarationRhsBoundaryOwner::StrictIndentedDedent,
        );
        let (direct_rhs, records, direct_remainder) = parse_type_declaration_rhs_boundary_direct(
            source,
            0,
            StopKind::RightBracket,
            TypeDeclarationRhsBoundaryOwner::StrictIndentedDedent,
        );
        assert!(matches!(ast_rhs, Recovered::Incomplete));
        assert!(matches!(direct_rhs, Recovered::Incomplete));
        assert_eq!(ast_remainder, "\nelse: 0");
        assert_eq!(direct_remainder, "\nelse: 0");
        assert_eq!(records, missing_rhs(9));

        // The RHS continuation baseline accepts only strictly deeper lines.
        for (source, expected_complete, expected_remainder) in [
            ("type Id =\n   Int", true, ""),
            ("type Id =\n  Int", false, "\n  Int"),
            ("type Id =\n Int", false, "\n Int"),
            ("type Id =\n   F\n    Int", true, ""),
            ("type Id =\n   Int ->\n    [e] T", true, ""),
        ] {
            let (ast_rhs, ast_remainder) = parse_type_declaration_rhs_boundary_ast(
                source,
                2,
                StopKind::RightBracket,
                TypeDeclarationRhsBoundaryOwner::None,
            );
            let (direct_rhs, records, direct_remainder) = parse_type_declaration_rhs_boundary_direct(
                source,
                2,
                StopKind::RightBracket,
                TypeDeclarationRhsBoundaryOwner::None,
            );
            assert_eq!(matches!(ast_rhs, Recovered::Complete(_)), expected_complete, "AST {source:?}");
            assert_eq!(matches!(direct_rhs, Recovered::Complete(_)), expected_complete, "direct {source:?}");
            assert_eq!(ast_remainder, expected_remainder, "AST {source:?}");
            assert_eq!(direct_remainder, expected_remainder, "direct {source:?}");
            assert_eq!(
                records,
                if expected_complete { vec![] } else { missing_rhs(9) },
                "direct {source:?}"
            );
        }

        // Each nested TypeExpression owner must leave the same companion gap
        // to Type's caller, including the malformed path-tail retry.
        for source in [
            "type Id = Int\nelse: 0",
            "type Id = F(X\nelse: 0",
            "type Id = (X\nelse: 0",
            "type Id = '[X\nelse: 0",
            "type Id = { value: Int\nelse: 0",
            "type Id = :{A\nelse: 0",
            "type Id = [e\nelse: 0",
            "type Id = T [e]\nelse: 0",
            "type Id = for 'a\nelse: 0",
            "type Id = Int ->\nelse: 0",
            "type Id = A::@\nelse: 0",
        ] {
            let (ast_rhs, ast_remainder) = parse_type_declaration_rhs_boundary_ast(
                source,
                0,
                StopKind::RightBracket,
                TypeDeclarationRhsBoundaryOwner::NestedIf,
            );
            let (direct_rhs, records, direct_remainder) = parse_type_declaration_rhs_boundary_direct(
                source,
                0,
                StopKind::RightBracket,
                TypeDeclarationRhsBoundaryOwner::NestedIf,
            );
            assert!(matches!(ast_rhs, Recovered::Complete(_)), "AST {source:?}");
            assert!(matches!(direct_rhs, Recovered::Complete(_)), "direct {source:?}");
            assert_eq!(ast_remainder, "\nelse: 0", "AST {source:?}");
            assert_eq!(direct_remainder, "\nelse: 0", "direct {source:?}");
            assert!(
                !records.iter().any(|(_, role, _)| *role == rhs_role),
                "nested recovery must retain its Type role: {source:?} => {records:#?}"
            );
            if source == "type Id = A::@\nelse: 0" {
                assert!(
                    records.iter().any(|(kind, role, range)| *kind == RecoveryKind::Error
                        && *role == GrammarRole::Type(crate::session::TypeRole::PathSegment)
                        && *range == (13..14)),
                    "malformed tail must not consume the companion boundary: {records:#?}"
                );
            }
        }

        // Fresh ParseLocals on consecutive runs prove the setup has no static
        // owner or stop-set residue between declarations.
        for _ in 0..2 {
            let (rhs, records, remainder) = parse_type_declaration_rhs_boundary_direct(
                "type Id = else: 0",
                0,
                StopKind::RightBracket,
                TypeDeclarationRhsBoundaryOwner::NestedIf,
            );
            assert!(matches!(rhs, Recovered::Incomplete));
            assert_eq!(remainder, " else: 0");
            assert_eq!(records, missing_rhs(9));
        }
    }

    #[test]
    fn type_declaration_td_r_worked_examples_are_lossless_and_byte_exact() {
        fn parse_ast<'source>(
            source: &'source str,
        ) -> (
            ParsedTypeDeclarationHeader<'source>,
            Vec<TypeDeclarationHeaderRecovery>,
            Recovered<Box<TypeExpression<'source>>>,
            String,
        ) {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            let mut expectations = chasa::LatestSink::new();
            let mut is_cut = false;
            let (header, recoveries, rhs) = {
                let mut i = In::new(
                    &mut source_input,
                    &mut expectations,
                    IsCut::new(&mut is_cut),
                )
                .set_local(&mut local);
                let intro = i
                    .run(recognize_type_statement_intro)
                    .expect("Type introduction is recognized in the worked-example harness");
                let (header, recoveries) = parse_type_declaration_header_slots(&intro, &mut i);
                let rhs = parse_type_declaration_rhs(&header, intro.type_base, &mut i);
                (header, recoveries, rhs)
            };
            (header, recoveries, rhs, source_input.remainder().to_owned())
        }

        fn emit_pair_header<'parse, 'source, 'local, E, O>(
            committed: &mut Committed<'parse, 'source, 'local, E, O>,
        ) where
            E: ErrorSink<usize>,
            O: CommitOutput<'source>,
        {
            committed.token(SyntaxKind::Whitespace, 4..5);
            committed.token(SyntaxKind::Identifier, 5..9);
            committed.start_node(SyntaxKind::DeclarationTypeParameterList);
            committed.token(SyntaxKind::Whitespace, 9..10);
            committed.token(SyntaxKind::SigilIdentifier, 10..15);
            committed.token(SyntaxKind::Whitespace, 15..16);
            committed.token(SyntaxKind::SigilIdentifier, 16..22);
            committed.finish_node();
            committed.token(SyntaxKind::Whitespace, 22..23);
            committed.token(SyntaxKind::Equals, 23..24);
        }

        fn emit_result_header<'parse, 'source, 'local, E, O>(
            committed: &mut Committed<'parse, 'source, 'local, E, O>,
        ) where
            E: ErrorSink<usize>,
            O: CommitOutput<'source>,
        {
            committed.token(SyntaxKind::Whitespace, 4..5);
            committed.token(SyntaxKind::Identifier, 5..11);
            committed.start_node(SyntaxKind::DeclarationTypeParameterList);
            committed.token(SyntaxKind::Whitespace, 11..12);
            committed.token(SyntaxKind::SigilIdentifier, 12..14);
            committed.finish_node();
            committed.token(SyntaxKind::Whitespace, 14..15);
            committed.token(SyntaxKind::Equals, 15..16);
        }

        fn parse_direct<'source>(
            source: &'source str,
        ) -> (
            ParsedTypeDeclarationHeader<'source>,
            Recovered<Range<usize>>,
            Vec<(RecoveryKind, GrammarRole, Range<usize>)>,
            String,
            SyntaxNode,
        ) {
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
                .run(recognize_type_statement_intro)
                .expect("Type introduction is recognized in the direct worked-example harness");
            let mut committed = probe.commit(FullCstOutput::new(source));
            committed.start_node(SyntaxKind::Root);
            committed.start_node(SyntaxKind::TypeDeclaration);
            committed.token(SyntaxKind::TypeKw, intro.type_keyword.range());
            let header = commit_type_declaration_header_slots(&intro, &mut committed);
            match source {
                "type Pair 'left 'right = ('left, 'right)" => emit_pair_header(&mut committed),
                "type Result 'a = ;" => emit_result_header(&mut committed),
                _ => unreachable!("only addendum worked examples use this direct CST harness"),
            }
            let rhs = commit_type_declaration_rhs(&header, intro.type_base, &mut committed);
            committed.finish_node();
            if source == "type Result 'a = ;" {
                committed.token(SyntaxKind::Semicolon, 17..18);
            }
            committed.finish_node();
            let remainder = committed.probe(|probe| probe.input().input.remainder().to_owned());
            let output = committed.into_output();
            let records = output
                .committed_recoveries()
                .iter()
                .map(|record| (record.kind, record.site.role, record.site.range.clone()))
                .collect();
            let root = SyntaxNode::new_root(output.finish_complete());
            (header, rhs, records, remainder, root)
        }

        fn parse_direct_header_and_rhs<'source>(
            source: &'source str,
        ) -> (
            ParsedTypeDeclarationHeader<'source>,
            Recovered<Range<usize>>,
            Vec<(RecoveryKind, GrammarRole, Range<usize>)>,
            String,
        ) {
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
                .run(recognize_type_statement_intro)
                .expect("Type introduction is recognized in the parity harness");
            let mut committed = probe.commit(HeaderOutput::new());
            let header = commit_type_declaration_header_slots(&intro, &mut committed);
            let rhs = commit_type_declaration_rhs(&header, intro.type_base, &mut committed);
            let remainder = committed.probe(|probe| probe.input().input.remainder().to_owned());
            let records = committed
                .into_output()
                .committed_recoveries()
                .iter()
                .map(|record| (record.kind, record.site.role, record.site.range.clone()))
                .collect();
            (header, rhs, records, remainder)
        }

        let pair = "type Pair 'left 'right = ('left, 'right)";
        let (ast_header, ast_recoveries, ast_rhs, ast_remainder) = parse_ast(pair);
        let (direct_header, direct_rhs, direct_records, direct_remainder, root) = parse_direct(pair);
        assert_eq!(ast_header, direct_header);
        assert!(ast_recoveries.is_empty());
        assert!(matches!(ast_header.name, Recovered::Complete(name) if name.text() == "Pair" && name.range() == (5..9)));
        assert!(matches!(ast_header.parameters.as_slice(), [
            DeclarationTypeParameter::SigilIdentifier(left),
            DeclarationTypeParameter::SigilIdentifier(right),
        ] if left.range() == (10..15) && right.range() == (16..22)));
        assert_eq!(ast_header.equals, Recovered::Complete(23..24));
        assert!(matches!(ast_rhs, Recovered::Complete(ref rhs) if rhs.range() == (25..40)));
        assert_eq!(direct_rhs, Recovered::Complete(25..40));
        assert_eq!(ast_remainder, "");
        assert_eq!(direct_remainder, "");
        assert!(direct_records.is_empty());
        assert_eq!(root.to_string(), pair);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() != SyntaxKind::Root)
                .map(|node| (node.kind(), syntax_range(node.text_range())))
                .collect::<Vec<_>>(),
            vec![
                (SyntaxKind::TypeDeclaration, 0..40),
                (SyntaxKind::DeclarationTypeParameterList, 9..22),
                (SyntaxKind::TypeExpression, 25..40),
                (SyntaxKind::ParenthesizedTypeGroup, 25..40),
                (SyntaxKind::TypeExpression, 26..31),
                (SyntaxKind::TypeExpression, 33..39),
            ]
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .map(|token| (token.kind(), token.text().to_owned(), syntax_range(token.text_range())))
                .collect::<Vec<_>>(),
            vec![
                (SyntaxKind::TypeKw, "type".to_owned(), 0..4),
                (SyntaxKind::Whitespace, " ".to_owned(), 4..5),
                (SyntaxKind::Identifier, "Pair".to_owned(), 5..9),
                (SyntaxKind::Whitespace, " ".to_owned(), 9..10),
                (SyntaxKind::SigilIdentifier, "'left".to_owned(), 10..15),
                (SyntaxKind::Whitespace, " ".to_owned(), 15..16),
                (SyntaxKind::SigilIdentifier, "'right".to_owned(), 16..22),
                (SyntaxKind::Whitespace, " ".to_owned(), 22..23),
                (SyntaxKind::Equals, "=".to_owned(), 23..24),
                (SyntaxKind::Whitespace, " ".to_owned(), 24..25),
                (SyntaxKind::LParen, "(".to_owned(), 25..26),
                (SyntaxKind::SigilIdentifier, "'left".to_owned(), 26..31),
                (SyntaxKind::Comma, ",".to_owned(), 31..32),
                (SyntaxKind::Whitespace, " ".to_owned(), 32..33),
                (SyntaxKind::SigilIdentifier, "'right".to_owned(), 33..39),
                (SyntaxKind::RParen, ")".to_owned(), 39..40),
            ]
        );

        let result = "type Result 'a = ;";
        let (ast_header, ast_recoveries, ast_rhs, ast_remainder) = parse_ast(result);
        let (direct_header, direct_rhs, direct_records, direct_remainder, root) = parse_direct(result);
        assert_eq!(ast_header, direct_header);
        assert!(ast_recoveries.is_empty());
        assert!(matches!(ast_header.name, Recovered::Complete(name) if name.text() == "Result" && name.range() == (5..11)));
        assert!(matches!(ast_header.parameters.as_slice(), [
            DeclarationTypeParameter::SigilIdentifier(parameter),
        ] if parameter.range() == (12..14)));
        assert_eq!(ast_header.equals, Recovered::Complete(15..16));
        assert!(matches!(ast_rhs, Recovered::Incomplete));
        assert_eq!(direct_rhs, Recovered::Incomplete);
        assert_eq!(ast_remainder, ";");
        assert_eq!(direct_remainder, ";");
        assert_eq!(direct_records, vec![
            (RecoveryKind::Missing, type_declaration_rhs_role(), 17..17),
        ]);
        assert_eq!(root.to_string(), result);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() != SyntaxKind::Root)
                .map(|node| (node.kind(), syntax_range(node.text_range())))
                .collect::<Vec<_>>(),
            vec![
                (SyntaxKind::TypeDeclaration, 0..17),
                (SyntaxKind::DeclarationTypeParameterList, 11..14),
                (SyntaxKind::TypeExpression, 17..17),
                (SyntaxKind::Missing, 17..17),
            ]
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .map(|token| (token.kind(), token.text().to_owned(), syntax_range(token.text_range())))
                .collect::<Vec<_>>(),
            vec![
                (SyntaxKind::TypeKw, "type".to_owned(), 0..4),
                (SyntaxKind::Whitespace, " ".to_owned(), 4..5),
                (SyntaxKind::Identifier, "Result".to_owned(), 5..11),
                (SyntaxKind::Whitespace, " ".to_owned(), 11..12),
                (SyntaxKind::SigilIdentifier, "'a".to_owned(), 12..14),
                (SyntaxKind::Whitespace, " ".to_owned(), 14..15),
                (SyntaxKind::Equals, "=".to_owned(), 15..16),
                (SyntaxKind::Whitespace, " ".to_owned(), 16..17),
                (SyntaxKind::Semicolon, ";".to_owned(), 17..18),
            ]
        );
        assert_eq!(
            root.children_with_tokens()
                .filter_map(|element| element.into_token())
                .map(|token| (token.kind(), syntax_range(token.text_range())))
                .collect::<Vec<_>>(),
            vec![(SyntaxKind::Semicolon, 17..18)],
            "the isolated root owns the statement separator outside TypeDeclaration"
        );

        // TD-R permits distinct slots to recover together, but never lets one
        // slot duplicate its own Missing/Error. Gates 4--6 already exhaust the
        // individual rows; these three cases make the composition explicit.
        for (source, expected_records, expected_remainder) in [
            (
                "type =;",
                vec![
                    (RecoveryKind::Missing, GrammarRole::Declaration(DeclarationRole::Type(TypeDeclarationRole::Name)), 5..5),
                    (RecoveryKind::Missing, type_declaration_rhs_role(), 6..6),
                ],
                ";",
            ),
            (
                "type Id = @;",
                vec![(
                    RecoveryKind::Error,
                    GrammarRole::Type(crate::session::TypeRole::Primary),
                    10..11,
                )],
                ";",
            ),
            (
                "type Id @;",
                vec![(
                    RecoveryKind::Error,
                    GrammarRole::Declaration(DeclarationRole::Type(TypeDeclarationRole::DefinitionIntroducer)),
                    8..9,
                )],
                ";",
            ),
        ] {
            let (ast_header, ast_recoveries, ast_rhs, ast_remainder) = parse_ast(source);
            let (direct_header, direct_rhs, direct_records, direct_remainder) =
                parse_direct_header_and_rhs(source);
            assert_eq!(ast_header, direct_header, "header parity for {source:?}");
            assert_eq!(ast_remainder, expected_remainder, "AST {source:?}");
            assert_eq!(direct_remainder, expected_remainder, "direct {source:?}");
            assert_eq!(direct_records, expected_records, "direct records for {source:?}");
            assert!(matches!(ast_rhs, Recovered::Incomplete), "AST {source:?}");
            assert!(matches!(direct_rhs, Recovered::Incomplete), "direct {source:?}");
            assert_eq!(
                ast_recoveries.len(),
                expected_records
                    .iter()
                    .filter(|(_, role, _)| {
                        matches!(
                            role,
                            GrammarRole::Declaration(DeclarationRole::Type(
                                TypeDeclarationRole::Name | TypeDeclarationRole::DefinitionIntroducer
                            ))
                        )
                    })
                    .count(),
                "AST header records for {source:?}",
            );
        }

        let source = "type Id 'a ('a)";
        let (ast_header, ast_recoveries, ast_rhs, ast_remainder) = parse_ast(source);
        let (direct_header, direct_rhs, direct_records, direct_remainder) =
            parse_direct_header_and_rhs(source);
        assert_eq!(ast_header, direct_header);
        assert_eq!(ast_recoveries.len(), 1);
        assert!(matches!(ast_rhs, Recovered::Complete(ref rhs) if rhs.range() == (11..15)));
        assert_eq!(direct_rhs, Recovered::Complete(11..15));
        assert_eq!(ast_remainder, "");
        assert_eq!(direct_remainder, "");
        assert_eq!(
            direct_records,
            vec![(
                RecoveryKind::Missing,
                GrammarRole::Declaration(DeclarationRole::Type(TypeDeclarationRole::DefinitionIntroducer)),
                11..11,
            )],
            "the missing '=' retries the RHS at the same parenthesized primary"
        );
    }

    #[test]
    fn type_declaration_is_reachable_from_root_and_nested_full_statement_dispatch() {
        fn parse_root_ast<'source>(source: &'source str) -> (TypeDeclaration<'source>, String) {
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
            let Some(Declaration::Type(declaration)) = i.run(parse_declaration) else {
                panic!("the root declaration dispatcher must select Type");
            };
            (declaration, i.input.remainder().to_owned())
        }

        fn parse_nested_ast<'source>(source: &'source str) -> (TypeDeclaration<'source>, String) {
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
            let table = crate::operator::OperatorTable::empty();
            let Some(Statement::Type(declaration)) =
                i.run(from_fn(|i| parse_canonical_statement(&table, i)))
            else {
                panic!("the nested canonical Statement dispatcher must select Type");
            };
            (declaration, i.input.remainder().to_owned())
        }

        let source = "type Pair 'left 'right = ('left, 'right)";
        let (root_declaration, root_remainder) = parse_root_ast(source);
        let (nested_declaration, nested_remainder) = parse_nested_ast(source);
        assert_eq!(root_declaration, nested_declaration);
        assert_eq!(root_remainder, "");
        assert_eq!(nested_remainder, "");
        assert_eq!(root_declaration.range, 0..40);
        assert!(matches!(root_declaration.name, Recovered::Complete(ref name) if name.range() == (5..9)));
        assert!(matches!(root_declaration.parameters.as_slice(), [
            DeclarationTypeParameter::SigilIdentifier(left),
            DeclarationTypeParameter::SigilIdentifier(right),
        ] if left.range() == (10..15) && right.range() == (16..22)));
        assert_eq!(root_declaration.equals, Recovered::Complete(23..24));
        assert!(matches!(root_declaration.rhs, Recovered::Complete(ref rhs) if rhs.range() == (25..40)));

        let output = parse_direct_root_candidate(
            source,
            &crate::operator::OperatorTable::empty(),
            &[],
        );
        assert!(output.committed_recoveries().is_empty());
        let root = SyntaxNode::new_root(output.green().clone());
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::TypeDeclaration)
                .map(|node| syntax_range(node.text_range()))
                .collect::<Vec<_>>(),
            vec![0..40],
        );

        let source_text: Arc<crate::SourceText> = Arc::from(source);
        let header = Arc::new(crate::scan_header(Arc::clone(&source_text)));
        let parsed = crate::parse_file(
            Arc::clone(&source_text),
            Arc::clone(&header),
            Arc::new(crate::SyntaxEnvironment::empty()),
        );
        assert_eq!(header.coverage().stop(), crate::HeaderStop::FirstNonHeader);
        assert!(parsed.diagnostics().is_empty());
        assert_eq!(SyntaxNode::new_root(parsed.green().clone()).to_string(), source);

        // A real braced Statement sequence proves the direct nested consumer
        // wraps the same declaration node rather than falling back to an
        // OperatorChain.  The following Binding also proves dispatch resumes.
        let nested_source = concat!(
            "my block = { type Pair 'left 'right = ('left, 'right); ",
            "my value = 1 }"
        );
        let nested_output = parse_direct_root_candidate(
            nested_source,
            &crate::operator::OperatorTable::empty(),
            &[],
        );
        assert!(nested_output.committed_recoveries().is_empty());
        let nested_root = SyntaxNode::new_root(nested_output.green().clone());
        assert_eq!(nested_root.to_string(), nested_source);
        let nested_type = nested_root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeDeclaration)
            .expect("the braced full-Statement sequence contains TypeDeclaration");
        assert_eq!(
            nested_type.parent().map(|parent| parent.kind()),
            Some(SyntaxKind::Statement),
        );
        assert_eq!(
            nested_root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::BindingStatement)
                .count(),
            2,
            "the outer and nested bindings both remain reachable",
        );
    }

    #[test]
    fn type_declaration_real_root_dispatch_preserves_semicolon_and_interleaving() {
        let result = "type Result 'a = ;";
        let mut source_input = SourceInput::new(result);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let Some(Declaration::Type(declaration)) = i.run(parse_declaration) else {
            panic!("the recovery worked example must select Type at root");
        };
        assert_eq!(declaration.range, 0..17);
        assert!(matches!(declaration.rhs, Recovered::Incomplete));
        assert_eq!(i.input.remainder(), ";");

        let output = parse_direct_root_candidate(
            result,
            &crate::operator::OperatorTable::empty(),
            &[],
        );
        let root = SyntaxNode::new_root(output.green().clone());
        assert_eq!(root.to_string(), result);
        assert_eq!(
            root.descendants()
                .find(|node| node.kind() == SyntaxKind::TypeDeclaration)
                .map(|node| syntax_range(node.text_range())),
            Some(0..17),
        );
        assert_eq!(
            root.children_with_tokens()
                .filter_map(|element| element.into_token())
                .map(|token| (token.kind(), syntax_range(token.text_range())))
                .collect::<Vec<_>>(),
            vec![(SyntaxKind::Semicolon, 17..18)],
            "the real root Statement loop, not TypeDeclaration, owns ';'",
        );
        let [record] = output.committed_recoveries() else {
            panic!("the missing RHS must produce exactly one recovery record");
        };
        assert_eq!(record.kind, RecoveryKind::Missing);
        assert_eq!(record.site.role, type_declaration_rhs_role());
        assert_eq!(record.site.range, 17..17);

        let interleaved = "my type Pair = Int;\nmy value = 1";
        let output = parse_direct_root_candidate(
            interleaved,
            &crate::operator::OperatorTable::empty(),
            &[],
        );
        assert!(output.committed_recoveries().is_empty());
        let root = SyntaxNode::new_root(output.green().clone());
        assert_eq!(root.to_string(), interleaved);
        assert_eq!(
            root.children()
                .filter(|node| {
                    matches!(
                        node.kind(),
                        SyntaxKind::TypeDeclaration | SyntaxKind::BindingStatement
                    )
                })
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            vec![SyntaxKind::TypeDeclaration, SyntaxKind::BindingStatement],
            "Type dispatch must leave the following root Binding candidate intact",
        );
    }

    #[test]
    fn type_declaration_stops_header_discovery_and_is_absent_from_operator_only_slots() {
        let source: Arc<crate::SourceText> = Arc::from("type Pair = Int\nuse std::data\n");
        let header = crate::scan_header(source);
        assert_eq!(header.coverage().stop(), crate::HeaderStop::FirstNonHeader);
        assert_eq!(header.coverage().range(), &(0..0));
        assert!(header.imports().is_empty());
        assert!(header.operators().is_empty());

        // Inline If bodies are real OperatorChain-only slots.  They may read
        // `type Pair` as ordinary expression words, but must never construct a
        // declaration or consume the exact-equals tail as one.
        let inline = "if condition: type Pair = Int";
        let mut source_input = SourceInput::new(inline);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        assert!(
            i.run(from_fn(|i| parse_expression_with_operators(
                &crate::operator::OperatorTable::empty(),
                i,
            )))
            .is_some()
        );
        assert_eq!(i.input.remainder(), " = Int");

        let mut source_input = SourceInput::new(inline);
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
        let mut committed = Probe::new(i).commit(RecordingOutput {
            calls: Rc::clone(&calls),
        });
        committed.start_node(SyntaxKind::Root);
        assert!(
            parse_direct_expression_with_operators(
                &crate::operator::OperatorTable::empty(),
                LeadingTrivia::None,
                &mut committed,
            )
            .is_some()
        );
        assert_eq!(
            committed.probe(|probe| probe.input().input.remainder()),
            " = Int",
        );
        committed.finish_node();
        let _ = committed.into_output();
        assert!(
            !calls
                .borrow()
                .iter()
                .any(|call| *call == OutputCall::Start(SyntaxKind::TypeDeclaration))
        );
    }

    #[test]
    fn struct_intro_commits_exact_keywords_before_binding_and_expression_fallback() {
        let table = crate::operator::OperatorTable::empty();
        let recognizes_struct = |source: &str| {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            let mut expectations = chasa::LatestSink::new();
            let mut is_cut = false;
            let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
                .set_local(&mut local);
            matches!(
                i.run(recognize_statement_intro),
                Some(StatementIntro::Struct(_))
            )
        };
        let parses_root_struct = |source: &str| {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            let mut expectations = chasa::LatestSink::new();
            let mut is_cut = false;
            let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
                .set_local(&mut local);
            matches!(
                i.run(parse_declaration),
                Some(Declaration::Struct(_))
            )
        };
        let parses_nested_struct = |source: &str| {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            let mut expectations = chasa::LatestSink::new();
            let mut is_cut = false;
            let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
                .set_local(&mut local);
            matches!(
                i.run(from_fn(|i| parse_canonical_statement(&table, i))),
                Some(Statement::Struct(_))
            )
        };
        for source in [
            "struct",
            "my struct",
            "our struct",
            "pub struct",
            "struct = value",
            "my struct = value",
        ] {
            assert!(recognizes_struct(source), "{source:?}");
            assert!(parses_root_struct(source), "{source:?}");
            assert!(parses_nested_struct(source), "{source:?}");

            let output = parse_direct_root_candidate(source, &table, &[]);
            let root = SyntaxNode::new_root(output.green().clone());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::StructDeclaration)
                    .count(),
                1,
                "{source:?}"
            );
            assert!(
                !root
                    .descendants()
                    .any(|node| node.kind() == SyntaxKind::BindingStatement),
                "{source:?}"
            );
        }

        for source in ["structure", "structural", "my_struct"] {
            assert!(!recognizes_struct(source), "{source:?}");

            let output = parse_direct_root_candidate(source, &table, &[]);
            let root = SyntaxNode::new_root(output.green().clone());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert!(
                !root
                    .descendants()
                    .any(|node| node.kind() == SyntaxKind::StructDeclaration),
                "{source:?}"
            );
        }
    }

    #[test]
    fn struct_header_recovery_hands_a_body_starter_forward_without_cascading() {
        let source = "struct @ {}";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        assert!(matches!(declaration.name, Recovered::Incomplete));
        assert!(matches!(
            declaration.body,
            Recovered::Complete(StructBody::NamedBraced(ref body))
                if body.open == (9..10)
                    && body.fields.is_empty()
                    && matches!(body.close, Recovered::Complete(ref close) if *close == (10..11))
        ));

        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let root = SyntaxNode::new_root(output.green().clone());
        assert_eq!(root.to_string(), source);
        assert!(root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::LBrace));
        let [record] = output.committed_recoveries() else {
            panic!("the malformed name is the only Struct recovery");
        };
        assert_eq!(record.kind, RecoveryKind::Error);
        assert_eq!(
            record.site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::Name))
        );
        assert_eq!(record.site.range, 7..9);

        let source = "struct S @";
        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let [record] = output.committed_recoveries() else {
            panic!("malformed body introducer must not cascade to Missing");
        };
        assert_eq!(record.kind, RecoveryKind::Error);
        assert_eq!(
            record.site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(
                crate::session::StructRole::BodyIntroducer,
            ))
        );
        assert_eq!(record.site.range, 9..10);
    }

    #[test]
    fn struct_header_slots_and_bodyless_form_are_typed_on_both_paths() {
        for (source, visibility, name_range, semicolon) in [
            ("struct S;", Visibility::Private, 7..8, 8..9),
            ("pub struct Marker;", Visibility::Public, 11..17, 17..18),
        ] {
            let (declaration, remainder) = parse_struct_for_test(source);
            assert_eq!(declaration.visibility, visibility, "{source:?}");
            assert!(matches!(declaration.name, Recovered::Complete(ref name) if name.range() == name_range), "{source:?}");
            assert!(matches!(declaration.body, Recovered::Complete(StructBody::Bodyless { semicolon: ref range }) if *range == semicolon), "{source:?}");
            assert_eq!(declaration.range, 0..semicolon.end, "{source:?}");
            assert_eq!(remainder, "", "{source:?}");

            let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
            let root = SyntaxNode::new_root(output.green().clone());
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(output.committed_recoveries().len(), 0, "{source:?}");
        }

        let output = parse_direct_root_candidate(
            "pub struct Marker;",
            &crate::operator::OperatorTable::empty(),
            &[],
        );
        let root = SyntaxNode::new_root(output.green().clone());
        let tokens: Vec<_> = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned(), syntax_range(token.text_range())))
            .collect();
        assert_eq!(tokens, vec![
            (SyntaxKind::PubKw, "pub".to_owned(), 0..3),
            (SyntaxKind::Whitespace, " ".to_owned(), 3..4),
            (SyntaxKind::StructKw, "struct".to_owned(), 4..10),
            (SyntaxKind::Whitespace, " ".to_owned(), 10..11),
            (SyntaxKind::Identifier, "Marker".to_owned(), 11..17),
            (SyntaxKind::Semicolon, ";".to_owned(), 17..18),
        ]);

        for (source, role, range) in [
            ("struct", crate::session::StructRole::Name, 6..6),
            ("struct;", crate::session::StructRole::Name, 6..6),
            ("struct S", crate::session::StructRole::BodyIntroducer, 8..8),
        ] {
            let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
            let [record] = output.committed_recoveries() else {
                panic!("one typed recovery expected for {source:?}");
            };
            assert_eq!(record.kind, RecoveryKind::Missing, "{source:?}");
            assert_eq!(
                record.site.role,
                GrammarRole::Declaration(DeclarationRole::Struct(role)),
                "{source:?}"
            );
            assert_eq!(record.site.range, range, "{source:?}");
        }

        let (declaration, remainder) = parse_struct_for_test("struct;");
        assert!(matches!(declaration.name, Recovered::Incomplete));
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::Bodyless { semicolon }) if semicolon == (6..7)));
        assert_eq!(remainder, "");

        let (declaration, remainder) = parse_struct_for_test("struct @ S;");
        assert!(matches!(declaration.name, Recovered::Complete(ref name) if name.range() == (9..10)));
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::Bodyless { semicolon }) if semicolon == (10..11)));
        assert_eq!(remainder, "");
        let output = parse_direct_root_candidate(
            "struct @ S;",
            &crate::operator::OperatorTable::empty(),
            &[],
        );
        let [record] = output.committed_recoveries() else {
            panic!("one Struct name error expected");
        };
        assert_eq!(record.kind, RecoveryKind::Error);
        assert_eq!(
            record.site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::Name))
        );
        assert_eq!(record.site.range, 7..9);

        for (source, expected_open) in [
            ("struct S {", 9..10),
            ("struct S(", 8..9),
            ("struct S:", 8..9),
        ] {
            let (declaration, remainder) = parse_struct_for_test(source);
            assert_eq!(remainder, "", "{source:?}");
            match declaration.body {
                Recovered::Complete(StructBody::NamedBraced(body)) => {
                    assert_eq!(body.open, expected_open);
                    assert!(body.fields.is_empty());
                    assert!(matches!(body.close, Recovered::Incomplete));
                }
                Recovered::Complete(StructBody::Tuple(body)) => {
                    assert_eq!(body.open, expected_open);
                    assert!(body.fields.is_empty());
                    assert!(matches!(body.close, Recovered::Incomplete));
                }
                Recovered::Complete(StructBody::NamedIndented(body)) => {
                    assert_eq!(body.colon, expected_open);
                    // A colon body has a mandatory first field slot.  Unlike
                    // the bracketed stubs above, its EOF recovery is already
                    // owned by the indented-body driver.
                    assert!(matches!(body.fields.as_slice(), [Recovered::Incomplete]));
                }
                _ => panic!("expected a recognized incomplete Struct body for {source:?}"),
            }
        }

        let (declaration, remainder) = parse_struct_for_test("struct S::");
        assert!(matches!(declaration.body, Recovered::Incomplete));
        assert_eq!(remainder, "::");
    }

    #[test]
    fn struct_named_brace_fields_keep_their_own_layout_and_type_apply_boundary() {
        let source = "struct Point { x: Int, y: List Int }";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        let Recovered::Complete(StructBody::NamedBraced(body)) = declaration.body else {
            panic!("expected named brace body");
        };
        assert_eq!(body.open, 13..14);
        assert_eq!(body.range, 13..36);
        assert_eq!(body.trailing_comma, None);
        assert!(matches!(body.close, Recovered::Complete(ref close) if *close == (35..36)));
        assert_eq!(body.fields.len(), 2);
        assert!(matches!(body.fields[0], Recovered::Complete(ref field) if field.range == (15..21)
            && matches!(field.name, Recovered::Complete(ref name) if name.range() == (15..16))
            && matches!(field.colon, Recovered::Complete(ref colon) if *colon == (16..17))));
        assert!(matches!(body.fields[1], Recovered::Complete(ref field) if field.range == (23..34)
            && matches!(field.name, Recovered::Complete(ref name) if name.range() == (23..24))
            && matches!(field.colon, Recovered::Complete(ref colon) if *colon == (24..25))));

        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let root = SyntaxNode::new_root(output.green().clone());
        assert_eq!(root.to_string(), source);
        assert_eq!(output.committed_recoveries().len(), 0);
        let tokens: Vec<_> = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned(), syntax_range(token.text_range())))
            .collect();
        assert_eq!(tokens, vec![
            (SyntaxKind::StructKw, "struct".to_owned(), 0..6),
            (SyntaxKind::Whitespace, " ".to_owned(), 6..7),
            (SyntaxKind::Identifier, "Point".to_owned(), 7..12),
            (SyntaxKind::Whitespace, " ".to_owned(), 12..13),
            (SyntaxKind::LBrace, "{".to_owned(), 13..14),
            (SyntaxKind::Whitespace, " ".to_owned(), 14..15),
            (SyntaxKind::Identifier, "x".to_owned(), 15..16),
            (SyntaxKind::Colon, ":".to_owned(), 16..17),
            (SyntaxKind::Whitespace, " ".to_owned(), 17..18),
            (SyntaxKind::Identifier, "Int".to_owned(), 18..21),
            (SyntaxKind::Comma, ",".to_owned(), 21..22),
            (SyntaxKind::Whitespace, " ".to_owned(), 22..23),
            (SyntaxKind::Identifier, "y".to_owned(), 23..24),
            (SyntaxKind::Colon, ":".to_owned(), 24..25),
            (SyntaxKind::Whitespace, " ".to_owned(), 25..26),
            (SyntaxKind::Identifier, "List".to_owned(), 26..30),
            (SyntaxKind::Whitespace, " ".to_owned(), 30..31),
            (SyntaxKind::Identifier, "Int".to_owned(), 31..34),
            (SyntaxKind::Whitespace, " ".to_owned(), 34..35),
            (SyntaxKind::RBrace, "}".to_owned(), 35..36),
        ]);
        assert_eq!(
            root.descendants().filter(|node| node.kind() == SyntaxKind::StructField).count(),
            2,
        );

        for source in ["struct S {}", "struct S { x: Int, }"] {
            let (declaration, remainder) = parse_struct_for_test(source);
            assert_eq!(remainder, "", "{source:?}");
            assert!(matches!(declaration.body, Recovered::Complete(StructBody::NamedBraced(ref body))
                if matches!(body.close, Recovered::Complete(_))), "{source:?}");
            let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
            assert_eq!(SyntaxNode::new_root(output.green().clone()).to_string(), source, "{source:?}");
        }

        let source = "struct S { x Int, y: Bool }";
        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        assert_eq!(SyntaxNode::new_root(output.green().clone()).to_string(), source);
        assert!(output.committed_recoveries().iter().any(|record|
            record.kind == RecoveryKind::Missing
                && record.site.role == GrammarRole::Declaration(DeclarationRole::Struct(
                    crate::session::StructRole::FieldColon,
                ))
                && record.site.range == (13..13)
        ));

        let separated = parse_struct_for_test("struct S { x: F y: Y }").0;
        let Recovered::Complete(StructBody::NamedBraced(separated)) = separated.body else {
            panic!("expected named brace body");
        };
        assert_eq!(separated.fields.len(), 2);
        let output = parse_direct_root_candidate(
            "struct S { x: F y: Y }",
            &crate::operator::OperatorTable::empty(),
            &[],
        );
        assert!(output.committed_recoveries().iter().any(|record|
            record.site.role == GrammarRole::Declaration(DeclarationRole::Struct(
                crate::session::StructRole::FieldSeparator,
            ))
        ));

        let applied = parse_struct_for_test("struct S { x: F Y }").0;
        let Recovered::Complete(StructBody::NamedBraced(applied)) = applied.body else {
            panic!("expected named brace body");
        };
        assert_eq!(applied.fields.len(), 1);
    }

    #[test]
    fn struct_named_fields_recover_colon_skeletons_without_cascading() {
        let (declaration, remainder) = parse_struct_for_test("struct S { @: Int }");
        assert_eq!(remainder, "");
        let Recovered::Complete(StructBody::NamedBraced(body)) = declaration.body else {
            panic!("expected named body");
        };
        let [Recovered::Complete(field)] = body.fields.as_slice() else {
            panic!("one recovered field expected");
        };
        assert!(matches!(field.name, Recovered::Incomplete));
        assert!(matches!(field.colon, Recovered::Complete(ref colon) if *colon == (12..13)));
        assert!(matches!(field.type_expr, Recovered::Complete(_)));

        let output = parse_direct_root_candidate(
            "struct S { @: Int }",
            &crate::operator::OperatorTable::empty(),
            &[],
        );
        let records = output.committed_recoveries();
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].kind, RecoveryKind::Error);
        assert_eq!(
            records[0].site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::FieldName)),
        );
        assert_eq!(records[0].site.range, 11..12);

        for (source, expected_range, colon_complete, type_complete) in [
            ("struct S { x @: Int }", 13..14, true, true),
            ("struct S { x @ Int }", 13..14, false, true),
            ("struct S { x @ }", 13..14, false, false),
        ] {
            let (declaration, remainder) = parse_struct_for_test(source);
            assert_eq!(remainder, "", "{source:?}");
            let Recovered::Complete(StructBody::NamedBraced(body)) = declaration.body else {
                panic!("expected named body for {source:?}");
            };
            let [Recovered::Complete(field)] = body.fields.as_slice() else {
                panic!("one recovered field expected for {source:?}");
            };
            assert_eq!(matches!(field.colon, Recovered::Complete(_)), colon_complete, "{source:?}");
            assert_eq!(matches!(field.type_expr, Recovered::Complete(_)), type_complete, "{source:?}");

            let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
            let records = output.committed_recoveries();
            assert_eq!(records.len(), 1, "{source:?}");
            assert_eq!(records[0].kind, RecoveryKind::Error, "{source:?}");
            assert_eq!(
                records[0].site.role,
                GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::FieldColon)),
                "{source:?}",
            );
            assert_eq!(records[0].site.range, expected_range, "{source:?}");
        }
    }

    #[test]
    fn struct_named_brace_semicolon_is_an_error_separator_and_retries_the_next_field() {
        let source = "struct S { x: Int; y: Bool }";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        let Recovered::Complete(StructBody::NamedBraced(body)) = declaration.body else {
            panic!("expected named body");
        };
        assert_eq!(body.fields.len(), 2);
        assert!(matches!(body.close, Recovered::Complete(ref close) if *close == (27..28)));
        assert!(matches!(body.fields.as_slice(), [Recovered::Complete(_), Recovered::Complete(_)]));

        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        assert_eq!(SyntaxNode::new_root(output.green().clone()).to_string(), source);
        let [record] = output.committed_recoveries() else {
            panic!("one separator error expected");
        };
        assert_eq!(record.kind, RecoveryKind::Error);
        assert_eq!(
            record.site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::FieldSeparator)),
        );
        assert_eq!(record.site.range, 17..18);
    }

    #[test]
    fn struct_named_field_boundary_does_not_cascade_a_missing_colon_into_a_missing_type() {
        let source = "struct S { x\n}";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        let Recovered::Complete(StructBody::NamedBraced(body)) = declaration.body else {
            panic!("expected named body");
        };
        let [Recovered::Complete(field)] = body.fields.as_slice() else {
            panic!("one field expected");
        };
        assert!(matches!(field.name, Recovered::Complete(_)));
        assert!(matches!(field.colon, Recovered::Incomplete));
        assert!(matches!(field.type_expr, Recovered::Incomplete));
        assert!(matches!(body.close, Recovered::Complete(ref close) if *close == (13..14)));

        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        assert_eq!(SyntaxNode::new_root(output.green().clone()).to_string(), source);
        let [record] = output.committed_recoveries() else {
            panic!("one missing field colon expected");
        };
        assert_eq!(record.kind, RecoveryKind::Missing);
        assert_eq!(
            record.site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::FieldColon)),
        );
        assert_eq!(record.site.range, 12..12);

        let source = "struct S:\n  x\nnext";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "\nnext");
        let Recovered::Complete(StructBody::NamedIndented(body)) = declaration.body else {
            panic!("expected named indented body");
        };
        let [Recovered::Complete(field)] = body.fields.as_slice() else {
            panic!("one field expected");
        };
        assert!(matches!(field.colon, Recovered::Incomplete));
        assert!(matches!(field.type_expr, Recovered::Incomplete));

        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let records = output.committed_recoveries();
        let struct_records: Vec<_> = records
            .iter()
            .filter(|record| matches!(record.site.role, GrammarRole::Declaration(DeclarationRole::Struct(_))))
            .collect();
        let [record] = struct_records.as_slice() else {
            panic!("one Struct recovery expected: {struct_records:#?}");
        };
        assert_eq!(record.kind, RecoveryKind::Missing);
        assert_eq!(
            record.site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::FieldColon)),
        );
        assert_eq!(record.site.range, 13..13);
    }

    #[test]
    fn struct_named_field_colon_recovery_keeps_double_colon_as_one_malformed_run() {
        let source = "struct S { name::Type }";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        let Recovered::Complete(StructBody::NamedBraced(body)) = declaration.body else {
            panic!("expected named body");
        };
        let [Recovered::Complete(field)] = body.fields.as_slice() else {
            panic!("one field expected");
        };
        assert!(matches!(field.name, Recovered::Complete(ref name) if name.range() == (11..15)));
        assert!(matches!(field.colon, Recovered::Incomplete));
        assert!(matches!(field.type_expr, Recovered::Complete(_)));
        assert!(matches!(body.close, Recovered::Complete(ref close) if *close == (22..23)));

        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        assert_eq!(SyntaxNode::new_root(output.green().clone()).to_string(), source);
        let [record] = output.committed_recoveries() else {
            panic!("one malformed field colon expected");
        };
        assert_eq!(record.kind, RecoveryKind::Error);
        assert_eq!(
            record.site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::FieldColon)),
        );
        assert_eq!(record.site.range, 15..17);
    }

    #[test]
    fn struct_named_brace_separator_before_eof_owns_distinct_field_and_close_slots() {
        let source = "struct S { x: Int,";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        let Recovered::Complete(StructBody::NamedBraced(body)) = declaration.body else {
            panic!("expected named body");
        };
        assert!(matches!(body.fields.as_slice(), [Recovered::Complete(_), Recovered::Incomplete]));
        assert!(matches!(body.close, Recovered::Incomplete));

        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let records = output.committed_recoveries();
        assert_eq!(records.len(), 2);
        assert_eq!(records[0].kind, RecoveryKind::Missing);
        assert_eq!(
            records[0].site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::Field)),
        );
        assert_eq!(records[0].site.range, 18..18);
        assert_eq!(records[1].kind, RecoveryKind::Missing);
        assert_eq!(
            records[1].site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::StructNamedFields,
                delimiter: Delimiter::Brace,
            },
        );
        assert_eq!(records[1].site.range, 18..18);

        let source = "struct S { x: Int\n";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        let Recovered::Complete(StructBody::NamedBraced(body)) = declaration.body else {
            panic!("expected named body");
        };
        assert!(matches!(body.fields.as_slice(), [Recovered::Complete(_), Recovered::Incomplete]));
        assert!(matches!(body.close, Recovered::Incomplete));

        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let records = output.committed_recoveries();
        assert_eq!(records.len(), 2);
        assert_eq!(
            records[0].site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::Field)),
        );
        assert_eq!(records[0].site.range, 18..18);
        assert_eq!(
            records[1].site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::StructNamedFields,
                delimiter: Delimiter::Brace,
            },
        );
        assert_eq!(records[1].site.range, 18..18);

        let source = "struct S { x: Int, ]";
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_stop_set(crate::session::StopSet::default().with(StopKind::RightBracket));
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let declaration = i.run(parse_struct_declaration).expect("Struct authority");
        assert_eq!(i.input.remainder(), "]");
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::NamedBraced(ref body))
            if matches!(body.fields.as_slice(), [Recovered::Complete(_), Recovered::Incomplete])
                && matches!(body.close, Recovered::Incomplete)));

        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_stop_set(crate::session::StopSet::default().with(StopKind::RightBracket));
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let mut committed = Probe::new(i).commit(FullCstOutput::new(source));
        let intro = committed
            .probe(|probe| probe.input().run(recognize_struct_statement_intro))
            .expect("Struct introduction");
        let _ = commit_struct_declaration(&mut committed, intro);
        let output = committed.into_output();
        let records = output.committed_recoveries();
        assert_eq!(records.len(), 2);
        assert_eq!(
            records[0].site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::Field)),
        );
        assert_eq!(records[0].site.range, 19..19);
        assert_eq!(
            records[1].site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::StructNamedFields,
                delimiter: Delimiter::Brace,
            },
        );
        assert_eq!(records[1].site.range, 19..19);
    }

    #[test]
    fn struct_named_field_invalid_run_yields_to_an_adjacent_valid_field_head() {
        let source = "struct S { @y: Int }";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        let Recovered::Complete(StructBody::NamedBraced(body)) = declaration.body else {
            panic!("expected named body");
        };
        assert!(matches!(body.fields.as_slice(), [Recovered::Incomplete, Recovered::Complete(field)]
            if matches!(field.name, Recovered::Complete(ref name) if name.range() == (12..13))
                && matches!(field.colon, Recovered::Complete(ref colon) if *colon == (13..14))
                && matches!(field.type_expr, Recovered::Complete(_))));

        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        assert_eq!(SyntaxNode::new_root(output.green().clone()).to_string(), source);
        let [record] = output.committed_recoveries() else {
            panic!("one whole-field error expected");
        };
        assert_eq!(record.kind, RecoveryKind::Error);
        assert_eq!(
            record.site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::Field)),
        );
        assert_eq!(record.site.range, 11..12);
    }

    #[test]
    fn struct_named_field_sequence_owns_leading_and_repeated_empty_comma_slots() {
        for (source, missing_ranges, field_count) in [
            ("struct S { ,x: Int }", vec![11..11], 2),
            ("struct S { x: Int,,y: Int }", vec![18..18], 3),
        ] {
            let (declaration, remainder) = parse_struct_for_test(source);
            assert_eq!(remainder, "", "{source:?}");
            let Recovered::Complete(StructBody::NamedBraced(body)) = declaration.body else {
                panic!("expected named body for {source:?}");
            };
            assert_eq!(body.fields.len(), field_count, "{source:?}");
            assert_eq!(
                body.fields.iter().filter(|field| matches!(field, Recovered::Incomplete)).count(),
                missing_ranges.len(),
                "{source:?}",
            );

            let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
            let records: Vec<_> = output
                .committed_recoveries()
                .iter()
                .filter(|record| {
                    record.kind == RecoveryKind::Missing
                        && record.site.role == GrammarRole::Declaration(DeclarationRole::Struct(
                            crate::session::StructRole::Field,
                        ))
                })
                .collect();
            assert_eq!(records.len(), missing_ranges.len(), "{source:?}");
            assert_eq!(
                records.iter().map(|record| record.site.range.clone()).collect::<Vec<_>>(),
                missing_ranges,
                "{source:?}",
            );
            let root = SyntaxNode::new_root(output.green().clone());
            assert_eq!(
                root.descendants().filter(|node| node.kind() == SyntaxKind::StructField).count(),
                field_count,
                "{source:?}",
            );
        }
    }

    #[test]
    fn struct_named_brace_close_recovery_keeps_local_and_outer_closers_distinct() {
        let source = "struct S { ] }";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::NamedBraced(ref body))
            if body.fields.is_empty() && matches!(body.close, Recovered::Complete(ref close) if *close == (13..14))));
        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let [record] = output.committed_recoveries() else {
            panic!("one local close error expected");
        };
        assert_eq!(record.kind, RecoveryKind::Error);
        assert_eq!(
            record.site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::StructNamedFields,
                delimiter: Delimiter::Brace,
            },
        );
        assert_eq!(record.site.range, 11..12);

        let source = "struct S { x: Int ] }";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::NamedBraced(ref body))
            if body.fields.len() == 1
                && matches!(body.close, Recovered::Complete(ref close) if *close == (20..21))));
        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let [record] = output.committed_recoveries() else {
            panic!("one local close error expected");
        };
        assert_eq!(record.kind, RecoveryKind::Error);
        assert_eq!(
            record.site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::StructNamedFields,
                delimiter: Delimiter::Brace,
            },
        );
        assert_eq!(record.site.range, 18..19);
        let root = SyntaxNode::new_root(output.green().clone());
        assert_eq!(root.to_string(), source);

        let source = "struct S { x: Int ]";
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_stop_set(crate::session::StopSet::default().with(StopKind::RightBracket));
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let declaration = i.run(parse_struct_declaration).expect("Struct authority");
        assert_eq!(i.input.remainder(), "]");
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::NamedBraced(ref body))
            if matches!(body.fields.as_slice(), [Recovered::Complete(_)])
                && matches!(body.close, Recovered::Incomplete)));

        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_stop_set(crate::session::StopSet::default().with(StopKind::RightBracket));
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let mut committed = Probe::new(i).commit(FullCstOutput::new(source));
        let intro = committed
            .probe(|probe| probe.input().run(recognize_struct_statement_intro))
            .expect("Struct introduction");
        let _ = commit_struct_declaration(&mut committed, intro);
        let output = committed.into_output();
        let [record] = output.committed_recoveries() else {
            panic!("one outer-owned missing close expected");
        };
        assert_eq!(record.kind, RecoveryKind::Missing);
        assert_eq!(
            record.site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::StructNamedFields,
                delimiter: Delimiter::Brace,
            },
        );
        assert_eq!(record.site.range, 18..18);

        let source = "struct S { @ ]";
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_stop_set(crate::session::StopSet::default().with(StopKind::RightBracket));
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let declaration = i.run(parse_struct_declaration).expect("Struct authority");
        assert_eq!(i.input.remainder(), "]");
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::NamedBraced(ref body))
            if matches!(body.fields.as_slice(), [Recovered::Incomplete])
                && matches!(body.close, Recovered::Incomplete)));

        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_stop_set(crate::session::StopSet::default().with(StopKind::RightBracket));
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let mut committed = Probe::new(i).commit(FullCstOutput::new(source));
        let intro = committed
            .probe(|probe| probe.input().run(recognize_struct_statement_intro))
            .expect("Struct introduction");
        let _ = commit_struct_declaration(&mut committed, intro);
        let output = committed.into_output();
        let records = output.committed_recoveries();
        assert_eq!(records.len(), 2);
        assert_eq!(records[0].kind, RecoveryKind::Error);
        assert_eq!(
            records[0].site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::Field)),
        );
        assert_eq!(records[0].site.range, 11..12);
        assert_eq!(records[1].kind, RecoveryKind::Missing);
        assert_eq!(
            records[1].site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::StructNamedFields,
                delimiter: Delimiter::Brace,
            },
        );
        assert_eq!(records[1].site.range, 13..13);
    }

    #[test]
    fn struct_named_indented_fields_keep_their_block_baseline_and_boundaries() {
        let source = "struct Point:\n  x: Int\n  y: String";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        let Recovered::Complete(StructBody::NamedIndented(body)) = declaration.body else {
            panic!("expected named indented body");
        };
        assert_eq!(body.colon, 12..13);
        assert_eq!(body.base_indent, 0);
        assert_eq!(body.block_indent, 2);
        assert_eq!(body.range, 12..34);
        assert_eq!(body.trailing_comma, None);
        assert!(matches!(body.fields.as_slice(), [
            Recovered::Complete(StructNamedField { range, .. }),
            Recovered::Complete(StructNamedField { range: second, .. }),
        ] if *range == (16..22) && *second == (25..34)));

        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let root = SyntaxNode::new_root(output.green().clone());
        assert_eq!(root.to_string(), source);
        assert!(output.committed_recoveries().is_empty());
        let tokens: Vec<_> = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned(), syntax_range(token.text_range())))
            .collect();
        assert_eq!(tokens, vec![
            (SyntaxKind::StructKw, "struct".to_owned(), 0..6),
            (SyntaxKind::Whitespace, " ".to_owned(), 6..7),
            (SyntaxKind::Identifier, "Point".to_owned(), 7..12),
            (SyntaxKind::Colon, ":".to_owned(), 12..13),
            (SyntaxKind::Newline, "\n".to_owned(), 13..14),
            (SyntaxKind::Whitespace, "  ".to_owned(), 14..16),
            (SyntaxKind::Identifier, "x".to_owned(), 16..17),
            (SyntaxKind::Colon, ":".to_owned(), 17..18),
            (SyntaxKind::Whitespace, " ".to_owned(), 18..19),
            (SyntaxKind::Identifier, "Int".to_owned(), 19..22),
            (SyntaxKind::Newline, "\n".to_owned(), 22..23),
            (SyntaxKind::Whitespace, "  ".to_owned(), 23..25),
            (SyntaxKind::Identifier, "y".to_owned(), 25..26),
            (SyntaxKind::Colon, ":".to_owned(), 26..27),
            (SyntaxKind::Whitespace, " ".to_owned(), 27..28),
            (SyntaxKind::Identifier, "String".to_owned(), 28..34),
        ]);
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::StructField).count(), 2);
    }

    #[test]
    fn struct_named_indented_recovery_keeps_dedent_and_field_slots_owned() {
        for source in ["struct S:", "struct S:\n  "] {
            let (declaration, remainder) = parse_struct_for_test(source);
            assert_eq!(remainder, "", "{source:?}");
            assert!(matches!(declaration.body, Recovered::Complete(StructBody::NamedIndented(ref body))
                if matches!(body.fields.as_slice(), [Recovered::Incomplete])), "{source:?}");
            let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
            let [record] = output.committed_recoveries() else {
                panic!("one first-field recovery expected for {source:?}");
            };
            assert_eq!(record.kind, RecoveryKind::Missing, "{source:?}");
            assert_eq!(
                record.site.role,
                GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::Field)),
                "{source:?}",
            );
        }

        let source = "struct S:\n  x:\n  y: Bool";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::NamedIndented(ref body))
            if body.block_indent == 2
                && matches!(body.fields.as_slice(), [Recovered::Complete(first), Recovered::Complete(second)]
                    if matches!(first.type_expr, Recovered::Incomplete)
                        && matches!(second.type_expr, Recovered::Complete(_)))));
        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let records = output.committed_recoveries();
        let [record] = records else { panic!("one missing type expected"); };
        assert_eq!(record.kind, RecoveryKind::Missing);
        assert_eq!(
            record.site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::FieldType)),
        );
        assert_eq!(record.site.range, 14..14);

        let source = "struct S:\n  x: Int, y: Bool,";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::NamedIndented(ref body))
            if body.fields.len() == 2 && body.trailing_comma == Some(27..28)));
        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        assert!(output.committed_recoveries().is_empty());
        assert_eq!(SyntaxNode::new_root(output.green().clone()).to_string(), source);

        let source = "struct S:\n  @\n  x: Int";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::NamedIndented(ref body))
            if matches!(body.fields.as_slice(), [Recovered::Incomplete, Recovered::Complete(_)])));
        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let [record] = output.committed_recoveries() else { panic!("one whole-field error expected"); };
        assert_eq!(record.kind, RecoveryKind::Error);
        assert_eq!(
            record.site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::Field)),
        );
        assert_eq!(record.site.range, 12..13);

        let (declaration, remainder) = parse_struct_for_test("struct S:\n  x: Int\nnext");
        assert_eq!(remainder, "\nnext");
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::NamedIndented(ref body))
            if body.fields.len() == 1));
    }

    #[test]
    fn struct_tuple_fields_keep_type_apply_and_tuple_close_ownership_distinct() {
        let source = "struct Pair(Int, List Int)";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        let Recovered::Complete(StructBody::Tuple(body)) = declaration.body else {
            panic!("expected tuple body");
        };
        assert_eq!(body.open, 11..12);
        assert_eq!(body.range, 11..26);
        assert_eq!(body.trailing_comma, None);
        assert!(matches!(body.close, Recovered::Complete(ref close) if *close == (25..26)));
        assert!(matches!(body.fields.as_slice(), [
            Recovered::Complete(StructTupleField { range, type_expr: Recovered::Complete(_) }),
            Recovered::Complete(StructTupleField { range: second, type_expr: Recovered::Complete(_) }),
        ] if *range == (12..15) && *second == (17..25)));

        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let root = SyntaxNode::new_root(output.green().clone());
        assert_eq!(root.to_string(), source);
        assert!(output.committed_recoveries().is_empty());
        let tokens: Vec<_> = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned(), syntax_range(token.text_range())))
            .collect();
        assert_eq!(tokens, vec![
            (SyntaxKind::StructKw, "struct".to_owned(), 0..6),
            (SyntaxKind::Whitespace, " ".to_owned(), 6..7),
            (SyntaxKind::Identifier, "Pair".to_owned(), 7..11),
            (SyntaxKind::LParen, "(".to_owned(), 11..12),
            (SyntaxKind::Identifier, "Int".to_owned(), 12..15),
            (SyntaxKind::Comma, ",".to_owned(), 15..16),
            (SyntaxKind::Whitespace, " ".to_owned(), 16..17),
            (SyntaxKind::Identifier, "List".to_owned(), 17..21),
            (SyntaxKind::Whitespace, " ".to_owned(), 21..22),
            (SyntaxKind::Identifier, "Int".to_owned(), 22..25),
            (SyntaxKind::RParen, ")".to_owned(), 25..26),
        ]);
        assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::StructField).count(), 2);

        for source in [
            "struct Pair()",
            "struct Pair(Int)",
            "struct Pair(Int,)",
            "struct Pair(\n  Int\n  Bool\n)",
        ] {
            let (declaration, remainder) = parse_struct_for_test(source);
            assert_eq!(remainder, "", "{source:?}");
            assert!(matches!(declaration.body, Recovered::Complete(StructBody::Tuple(ref body))
                if matches!(body.close, Recovered::Complete(_))), "{source:?}");
            let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
            assert_eq!(SyntaxNode::new_root(output.green().clone()).to_string(), source, "{source:?}");
            assert!(output.committed_recoveries().is_empty(), "{source:?}");
        }

        let applied = parse_struct_for_test("struct Pair(Int Bool)").0;
        assert!(matches!(applied.body, Recovered::Complete(StructBody::Tuple(ref body))
            if body.fields.len() == 1 && matches!(body.fields[0], Recovered::Complete(_))));
        let output = parse_direct_root_candidate(
            "struct Pair(Int Bool)",
            &crate::operator::OperatorTable::empty(),
            &[],
        );
        assert_eq!(
            SyntaxNode::new_root(output.green().clone())
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::StructField)
                .count(),
            1,
        );

        for (source, missing_ranges, field_count) in [
            ("struct Pair(,Int)", vec![12..12], 2),
            ("struct Pair(Int,, Bool)", vec![16..16], 3),
        ] {
            let (declaration, remainder) = parse_struct_for_test(source);
            assert_eq!(remainder, "", "{source:?}");
            assert!(matches!(declaration.body, Recovered::Complete(StructBody::Tuple(ref body))
                if body.fields.len() == field_count), "{source:?}");
            let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
            let records: Vec<_> = output.committed_recoveries().iter().filter(|record| {
                record.kind == RecoveryKind::Missing
                    && record.site.role == GrammarRole::Declaration(DeclarationRole::Struct(
                        crate::session::StructRole::FieldType,
                    ))
            }).collect();
            assert_eq!(records.iter().map(|record| record.site.range.clone()).collect::<Vec<_>>(), missing_ranges);
            let root = SyntaxNode::new_root(output.green().clone());
            assert_eq!(root.descendants().filter(|node| node.kind() == SyntaxKind::StructField).count(), field_count);
        }

        let source = "struct Pair(Int; Bool)";
        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let [record] = output.committed_recoveries() else {
            panic!("one tuple separator error expected");
        };
        assert_eq!(record.kind, RecoveryKind::Error);
        assert_eq!(
            record.site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::FieldSeparator)),
        );
        assert_eq!(record.site.range, 15..16);

        let (declaration, remainder) = parse_struct_for_test("struct Pair(Int; Bool)");
        assert_eq!(remainder, "");
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::Tuple(ref body))
            if body.fields.len() == 2 && matches!(body.close, Recovered::Complete(_))));

        let (declaration, remainder) = parse_struct_for_test("struct Pair(Int,");
        assert_eq!(remainder, "");
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::Tuple(ref body))
            if matches!(body.fields.as_slice(), [Recovered::Complete(_), Recovered::Incomplete])
                && matches!(body.close, Recovered::Incomplete)));
        let output = parse_direct_root_candidate(
            "struct Pair(Int,",
            &crate::operator::OperatorTable::empty(),
            &[],
        );
        assert_eq!(output.committed_recoveries().len(), 2);
        assert_eq!(output.committed_recoveries()[0].kind, RecoveryKind::Missing);
        assert_eq!(
            output.committed_recoveries()[0].site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::FieldType)),
        );
        assert_eq!(output.committed_recoveries()[0].site.range, 16..16);
        assert_eq!(
            output.committed_recoveries()[1].site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::StructTupleFields,
                delimiter: Delimiter::Parenthesis,
            },
        );
        assert_eq!(output.committed_recoveries()[1].site.range, 16..16);

        for (source, type_complete, error_range) in [
            ("struct Pair(@ Int)", true, 12..14),
            ("struct Pair(@)", false, 12..13),
        ] {
            let (declaration, remainder) = parse_struct_for_test(source);
            assert_eq!(remainder, "", "{source:?}");
            assert!(matches!(declaration.body, Recovered::Complete(StructBody::Tuple(ref body))
                if matches!(body.fields.as_slice(), [field] if matches!(field, Recovered::Complete(_)) == type_complete)),
                "{source:?}");
            let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
            let type_primary: Vec<_> = output.committed_recoveries().iter().filter(|record| {
                record.kind == RecoveryKind::Error
                    && record.site.role == GrammarRole::Type(crate::session::TypeRole::Primary)
            }).collect();
            assert_eq!(type_primary.len(), 1, "{source:?}");
            assert_eq!(type_primary[0].site.range, error_range, "{source:?}");
            assert!(!output.committed_recoveries().iter().any(|record| {
                record.kind == RecoveryKind::Missing
                    && record.site.role == GrammarRole::Declaration(DeclarationRole::Struct(
                        crate::session::StructRole::FieldType,
                    ))
            }), "{source:?}");
        }
    }

    #[test]
    fn struct_tuple_close_recovery_keeps_local_and_outer_closers_distinct() {
        let source = "struct Pair(Int] )";
        let (declaration, remainder) = parse_struct_for_test(source);
        assert_eq!(remainder, "");
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::Tuple(ref body))
            if body.fields.len() == 1 && matches!(body.close, Recovered::Complete(ref close) if *close == (17..18))));
        let output = parse_direct_root_candidate(source, &crate::operator::OperatorTable::empty(), &[]);
        let [record] = output.committed_recoveries() else {
            panic!("one local tuple-close error expected");
        };
        assert_eq!(record.kind, RecoveryKind::Error);
        assert_eq!(
            record.site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::StructTupleFields,
                delimiter: Delimiter::Parenthesis,
            },
        );
        assert_eq!(record.site.range, 15..16);

        let source = "struct Pair(@ ]";
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_stop_set(crate::session::StopSet::default().with(StopKind::RightBracket));
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let declaration = i.run(parse_struct_declaration).expect("Struct authority");
        assert_eq!(i.input.remainder(), "]");
        assert!(matches!(declaration.body, Recovered::Complete(StructBody::Tuple(ref body))
            if matches!(body.fields.as_slice(), [Recovered::Incomplete])
                && matches!(body.close, Recovered::Incomplete)));

        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_stop_set(crate::session::StopSet::default().with(StopKind::RightBracket));
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let mut committed = Probe::new(i).commit(FullCstOutput::new(source));
        let intro = committed
            .probe(|probe| probe.input().run(recognize_struct_statement_intro))
            .expect("Struct introduction");
        let _ = commit_struct_declaration(&mut committed, intro);
        let output = committed.into_output();
        let records = output.committed_recoveries();
        assert_eq!(records.len(), 2);
        assert_eq!(records[0].kind, RecoveryKind::Error);
        assert_eq!(records[0].site.role, GrammarRole::Type(crate::session::TypeRole::Primary));
        assert_eq!(records[0].site.range, 12..13);
        assert_eq!(records[1].kind, RecoveryKind::Missing);
        assert_eq!(
            records[1].site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::StructTupleFields,
                delimiter: Delimiter::Parenthesis,
            },
        );
        assert_eq!(records[1].site.range, 14..14);
    }

    #[test]
    fn source_leading_mod_ends_header_discovery_without_header_projection() {
        let source: Arc<crate::SourceText> = Arc::from("mod outer;");
        let header = crate::scan_header(source);
        assert_eq!(header.coverage().stop(), crate::HeaderStop::FirstNonHeader);
        assert!(header.imports().is_empty());
        assert!(header.operators().is_empty());
    }

    #[test]
    fn mod_identity_and_body_discriminator_are_binding_power_invariant() {
        let source = "mod outer { a + b }";
        let table = |power: crate::operator::BindingPower| {
            crate::operator::OperatorTable::from_declarations([
                crate::operator::OperatorDeclaration::new(
                    "+",
                    crate::operator::OperatorFixities::new().with_infix(power.clone(), power),
                ),
            ])
            .expect("operator table")
        };
        let low = table(crate::operator::BindingPower::scalar(1));
        let high = table(crate::operator::BindingPower::scalar(99));
        assert_eq!(
            parse_direct_root_candidate(source, &low, &[]).green(),
            parse_direct_root_candidate(source, &high, &[]).green(),
        );
    }

    fn parse_struct_with_if_companion_for_test<'source>(
        source: &'source str,
    ) -> (StructDeclaration<'source>, String) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let root_scope = local.push_root_statement_ambient_scope();
        let block_scope = local.push_indented_statement_ambient_scope(2);
        let companion = local.push_if_expression_companion(0, &["elsif", "else"]);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let _ = i.run(scan_trivia).expect("trivia is total");
        let declaration = i
            .run(parse_struct_declaration)
            .expect("the Struct introduction must commit its header continuation");
        let remainder = i.input.remainder().to_owned();
        drop(i);
        assert_eq!(local.pop_if_expression_companion().map(|frame| frame.id()), Some(companion));
        assert_eq!(local.pop_ambient_owner_scope(), Some(block_scope));
        assert_eq!(local.pop_ambient_owner_scope(), Some(root_scope));
        (declaration, remainder)
    }

    #[test]
    fn struct_lists_leave_ambient_if_companions_for_the_statement_owner() {
        let (declaration, remainder) = parse_struct_with_if_companion_for_test(
            "  struct S { x: Int\nelse: 0",
        );
        assert_eq!(remainder, "\nelse: 0");
        assert!(matches!(
            declaration.body,
            Recovered::Complete(StructBody::NamedBraced(ref body))
                if body.fields.len() == 1 && matches!(body.close, Recovered::Incomplete)
        ));

        let (declaration, remainder) = parse_struct_with_if_companion_for_test(
            "  struct S { x: Int\n  else: Bool }",
        );
        assert_eq!(remainder, "\n  else: Bool }");
        assert!(matches!(
            declaration.body,
            Recovered::Complete(StructBody::NamedBraced(ref body))
                if body.fields.len() == 1 && matches!(body.close, Recovered::Incomplete)
        ));

        let (declaration, remainder) = parse_struct_with_if_companion_for_test(
            "  struct S { x: Int,\n  else: Bool }\nelse: 0",
        );
        assert_eq!(remainder, "\nelse: 0");
        assert!(matches!(
            declaration.body,
            Recovered::Complete(StructBody::NamedBraced(ref body))
                if body.fields.len() == 2 && matches!(body.close, Recovered::Complete(_))
        ));

        let (declaration, remainder) = parse_struct_with_if_companion_for_test(
            "  struct S(Int\nelse: 0",
        );
        assert_eq!(remainder, "\nelse: 0");
        assert!(matches!(
            declaration.body,
            Recovered::Complete(StructBody::Tuple(ref body))
                if body.fields.len() == 1 && matches!(body.close, Recovered::Incomplete)
        ));
    }

    #[test]
    fn direct_struct_lists_keep_if_companions_and_comma_authority_distinct() {
        let table = crate::operator::OperatorTable::empty();
        for (source, fields, expected_close_role) in [
            (
                "if condition:\n  struct S { x: Int\nelse: 0",
                1,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::StructNamedFields,
                    delimiter: Delimiter::Brace,
                },
            ),
            (
                "if condition:\n  struct S(Int\nelse: 0",
                1,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::StructTupleFields,
                    delimiter: Delimiter::Parenthesis,
                },
            ),
        ] {
            let (root, recoveries) = parse_direct_expression_for_struct_test(source, &table);
            assert_eq!(root.to_string(), source, "{source:?}");
            assert_eq!(
                root.descendants_with_tokens()
                    .filter_map(|element| element.into_token())
                    .filter(|token| token.kind() == SyntaxKind::ElseKw)
                    .count(),
                1,
                "{source:?}",
            );
            let declaration = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::StructDeclaration)
                .expect("one Struct declaration");
            assert_eq!(
                declaration
                    .descendants()
                    .filter(|node| node.kind() == SyntaxKind::StructField)
                    .count(),
                fields,
                "{source:?}",
            );
            assert_eq!(
                recoveries.iter().filter(|record| {
                    record.kind == RecoveryKind::Missing && record.site.role == expected_close_role
                }).count(),
                1,
                "{source:?}",
            );
        }

        // The active If companion deliberately wins even at the Struct
        // field-list column.  The recovered Struct leaves its unmatched `}`
        // for the surrounding statement owner, so this direct expression
        // probe intentionally observes that exact unconsumed tail.
        let source = "if condition:\n  struct S { x: Int\n  else: Bool }";
        let (remainder, recoveries) = parse_direct_expression_prefix_for_struct_test(source, &table);
        assert_eq!(remainder, " }");
        assert_eq!(
            recoveries.iter().filter(|record| {
                record.kind == RecoveryKind::Missing
                    && record.site.role
                        == GrammarRole::ClosingDelimiter {
                            owner: ConstructRole::StructNamedFields,
                            delimiter: Delimiter::Brace,
                        }
            }).count(),
            1,
        );

        let source = "if condition:\n  struct S { x: Int,\n  else: Bool }\nelse: 0";
        let (root, recoveries) = parse_direct_expression_for_struct_test(source, &table);
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::ElseKw)
                .count(),
            1,
        );
        let declaration = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::StructDeclaration)
            .expect("one Struct declaration");
        assert_eq!(
            declaration
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::StructField)
                .count(),
            2,
        );
        assert!(!recoveries.iter().any(|record| {
            record.site.role
                == GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::StructNamedFields,
                    delimiter: Delimiter::Brace,
                }
        }));
    }

    fn parse_direct_expression_for_struct_test(
        source: &str,
        table: &crate::operator::OperatorTable,
    ) -> (SyntaxNode, Vec<CommittedRecoveryRecord>) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let mut committed = Probe::new(i).commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        parse_direct_expression_with_operators(table, LeadingTrivia::None, &mut committed)
            .expect("direct If expression");
        assert_eq!(committed.probe(|probe| probe.input().input.remainder()), "", "{source:?}");
        committed.finish_node();
        let output = committed.into_output();
        let recoveries = output.committed_recoveries().to_vec();
        let root = SyntaxNode::new_root(output.finish_complete());
        (root, recoveries)
    }

    fn parse_direct_expression_prefix_for_struct_test(
        source: &str,
        table: &crate::operator::OperatorTable,
    ) -> (String, Vec<CommittedRecoveryRecord>) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let mut committed = Probe::new(i).commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        parse_direct_expression_with_operators(table, LeadingTrivia::None, &mut committed)
            .expect("direct If expression");
        let remainder = committed.probe(|probe| probe.input().input.remainder().to_owned());
        committed.finish_node();
        let output = committed.into_output();
        (remainder, output.committed_recoveries().to_vec())
    }

    fn parse_struct_for_test<'source>(source: &'source str) -> (StructDeclaration<'source>, String) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let declaration = i
            .run(parse_struct_declaration)
            .expect("the Struct introduction must commit its header continuation");
        (declaration, i.input.remainder().to_owned())
    }

    fn parse_mod(source: &str) -> (ModDeclaration<'_>, &str) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let table = crate::operator::OperatorTable::empty();
        let declaration = i.run(from_fn(|i| parse_mod_declaration_with_operators(&table, i)))
            .expect("mod declaration should parse");
        (declaration, i.input.remainder())
    }

    fn parses_mod(source: &str) -> bool {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
            .set_local(&mut local);
        let table = crate::operator::OperatorTable::empty();
        i.run(from_fn(|i| parse_mod_declaration_with_operators(&table, i))).is_some()
    }

    #[test]
    fn bindings_accept_every_visibility_optional_definition_and_pattern_target() {
        for (source, visibility, has_definition, target_range) in [
            ("my value", Visibility::Private, false, 3..8),
            ("our (left, right) = pair", Visibility::Our, true, 4..17),
            ("pub [head, tail] = values", Visibility::Public, true, 4..16),
            ("my {left, right} = record", Visibility::Private, true, 3..16),
        ] {
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

            let Some(Declaration::Binding(binding)) = i.run(parse_declaration) else {
                panic!("expected binding for {source:?}");
            };
            assert_eq!(binding.visibility(), visibility, "{source:?}");
            assert!(matches!(binding.target(), Recovered::Complete(target) if target.range() == target_range), "{source:?}");
            assert_eq!(binding.definition().is_some(), has_definition, "{source:?}");
            assert_eq!(i.input.remainder(), "", "{source:?}");
        }
    }

    #[test]
    fn binding_indented_body_reuses_the_canonical_statement_dispatch() {
        let source = "our item =\n  my nested = value\n  use std\n  mod nested;";
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

        let Some(Declaration::Binding(binding)) = i.run(parse_declaration) else {
            panic!("expected binding declaration");
        };
        let Some(definition) = binding.definition() else { panic!("expected definition"); };
        let Recovered::Complete(BindingBody::Indented { block }) = definition.body() else {
            panic!("expected indented binding body");
        };
        assert!(matches!(block.statements(), [
            Recovered::Complete(crate::grammar::expression::Statement::Binding(_)),
            Recovered::Complete(crate::grammar::expression::Statement::Use(_)),
            Recovered::Complete(crate::grammar::expression::Statement::Mod(_)),
        ]));
        assert_eq!(i.input.remainder(), "");
    }

    #[test]
    fn visibility_prefixed_use_is_selected_only_with_a_valid_use_tree() {
        for source in ["my use = value", "our use = value", "pub use = value"] {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            let mut expectations = chasa::LatestSink::new();
            let mut is_cut = false;
            let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
                .set_local(&mut local);
            assert!(matches!(i.run(parse_declaration), Some(Declaration::Binding(_))), "{source:?}");
            assert_eq!(i.input.remainder(), "", "{source:?}");
        }
        for source in ["my use std", "our use std", "pub use std"] {
            let mut source_input = SourceInput::new(source);
            let mut local = ParseLocal::new();
            let mut expectations = chasa::LatestSink::new();
            let mut is_cut = false;
            let mut i = In::new(&mut source_input, &mut expectations, IsCut::new(&mut is_cut))
                .set_local(&mut local);
            assert!(matches!(i.run(parse_declaration), Some(Declaration::Use(_))), "{source:?}");
            assert_eq!(i.input.remainder(), "", "{source:?}");
        }
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

//! Shared grammar for source-leading declarations.

use std::{ops::Range, sync::Arc};

use chasa::{
    Back as _, ErrorSink, Input as _,
    error::std::{Unexpected, UnexpectedEndOfInput},
    input::IsCut,
    parser::Parser as _,
    prelude::{In, from_fn, item},
};

use crate::{
    BindingPower as HeaderBindingPower, BindingPowers, HeaderImport, HeaderImportForm,
    HeaderImportRoute, HeaderImportRouteSeparator, HeaderOperator, Visibility,
    grammar::expression::{
        BracedStatementBlockExpression, IndentedStatementBlock, IntroducedBodyLayout,
        OperatorChain, ParsedExpression, Statement, commit_braced_statement_block_expression,
        commit_canonical_statement, commit_indented_act_body, commit_indented_binding_body,
        commit_indented_cast_body, commit_indented_for_body, commit_indented_impl_tail_body,
        commit_indented_mod_body, commit_indented_role_body,
        parse_braced_statement_block_expression, parse_canonical_statement,
        parse_direct_expression_with_operators, parse_expression_with_operators,
        parse_indented_act_body, parse_indented_binding_body, parse_indented_cast_body,
        parse_indented_for_body, parse_indented_impl_tail_body, parse_indented_mod_body,
        parse_indented_role_body, probe_apostrophe_sigil_word, recognize_introduced_body_layout,
    },
    grammar::{
        pattern::{
            ParsedPattern, Pattern, PatternMandatorySlotPolicy,
            commit_direct_pattern_with_outer_missing_role_and_policy,
            parse_direct_pattern_with_outer_missing_role, parse_pattern_with_outer_missing_role,
            parse_required_pattern_with_outer_missing_role_and_policy, pattern_nud_candidate_input,
        },
        type_expr::{
            TypeExpression, commit_direct_type_expression_with_outer_missing_role,
            commit_direct_type_expression_with_outer_missing_role_and_policy,
            parse_required_type_expression_with_outer_missing_role,
            parse_required_type_expression_with_outer_missing_role_and_policy,
            parse_type_expression, type_stop_is_active_in_current_episode,
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
        AmbientOwnerScopeKind, BindingRole, BracedBarrierOrigin, CastRole, CommitOutput, Committed,
        CommittedRecoveryRecord, ConstructRole, DeclarationRole, Delimiter, DerivesRole,
        EnumDeclarationRole, ErrorDeclarationRole, ExpectationSources, ExpectedSyntax,
        ForStatementRole, FullCstOutput, GrammarRole, ImplRole, ImportRole, IndentationBaseline,
        IndentationBaselineKind, LayoutDelimitedBoundary, LayoutDelimitedFrame, LayoutRole,
        ModRole, OperatorHeaderRole, ParseLocal, Probe, RecoveryKind, RecoverySiteKey,
        RootUnexpected, RootUnexpectedHead, StatementKind, StatementRole, StopKind, StopSet, SynIn,
        SyntaxExpectation, TypeDeclarationRole, TypeDelimitedOwner, TypeExpressionEpisodePolicy,
        TypeExpressionScopedStopFrame, UnexpectedSyntax, VariantDeclarationRole,
        any_ambient_owner_claims,
    },
    syntax_kind::SyntaxKind,
};

mod binding_style_body;
mod derives;
mod for_statement;
mod use_decl;

use binding_style_body::*;
use derives::*;
use for_statement::*;
use use_decl::*;

pub(crate) use for_statement::{
    ForStatement, commit_for_statement_isolated, parse_for_statement_isolated,
};
pub(crate) use use_decl::{UseDeclaration, commit_use_declaration, parse_use_declaration};

/// One parsed source-leading declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Declaration<'source> {
    Use(UseDeclaration<'source>),
    Binding(BindingDeclaration<'source>),
    OperatorHeader(OperatorHeaderDeclaration<'source>),
    Mod(ModDeclaration<'source>),
    Struct(StructDeclaration<'source>),
    Enum(EnumDeclaration<'source>),
    Error(ErrorDeclaration<'source>),
    Type(TypeDeclaration<'source>),
    Role(RoleDeclaration<'source>),
    Impl(ImplDeclaration<'source>),
    Cast(CastDeclaration<'source>),
    Act(ActDeclaration<'source>),
    For(ForStatement<'source>),
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
    #[allow(dead_code)]
    Enum(EnumStatementIntro<'source>),
    #[allow(dead_code)]
    Error(ErrorStatementIntro<'source>),
    Type(TypeStatementIntro<'source>),
    #[allow(dead_code)]
    Role(RoleStatementIntro<'source>),
    #[allow(dead_code)]
    Impl(ImplStatementIntro<'source>),
    #[allow(dead_code)]
    Cast(CastStatementIntro<'source>),
    #[allow(dead_code)]
    Act(ActStatementIntro<'source>),
    For(ForStatementIntro<'source>),
}

/// The sink-free prefix reserved for standalone Cast declarations.
///
/// Gate 1 carries this source shape only. Gate 2 supplies recognition, and
/// Gate 8 connects it to shared statement dispatch.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CastStatementIntro<'source> {
    start: usize,
    visibility: Option<VisibilityPrefix<'source>>,
    after_visibility: Option<TriviaRun>,
    cast_keyword: WordSpan<'source>,
    cast_base: usize,
}

/// The sink-free prefix reserved for standalone Role declarations.
///
/// Gate 1 carries this source shape only. Gate 2 supplies recognition, and
/// Gate 9 connects it to shared statement dispatch.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RoleStatementIntro<'source> {
    start: usize,
    visibility: Option<VisibilityPrefix<'source>>,
    after_visibility: Option<TriviaRun>,
    role_keyword: WordSpan<'source>,
    role_base: usize,
}

/// The sink-free prefix reserved for standalone Act declarations.
///
/// Gate 1 carries this source shape only. Gate 2 supplies recognition, and
/// Gate 10 connects it to shared statement dispatch.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ActStatementIntro<'source> {
    start: usize,
    visibility: Option<VisibilityPrefix<'source>>,
    after_visibility: Option<TriviaRun>,
    act_keyword: WordSpan<'source>,
    act_base: usize,
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

/// The sink-free prefix reserved for standalone Enum declarations.
///
/// Gate 1 carries this source shape only. Gate 2 supplies recognition, and
/// Gate 11 connects it to shared statement dispatch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EnumStatementIntro<'source> {
    start: usize,
    visibility: Option<VisibilityPrefix<'source>>,
    after_visibility: Option<TriviaRun>,
    enum_keyword: WordSpan<'source>,
    enum_base: usize,
}

/// The sink-free prefix reserved for standalone Error declarations.
///
/// Gate 1 carries this source shape only. Gate 2 supplies recognition, and
/// Gate 9 connects it to shared statement dispatch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ErrorStatementIntro<'source> {
    start: usize,
    visibility: Option<VisibilityPrefix<'source>>,
    after_visibility: Option<TriviaRun>,
    error_keyword: WordSpan<'source>,
    error_base: usize,
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

/// The sink-free prefix reserved for standalone Impl declarations.
///
/// Gate 1 carries this source shape only. Gate 2 supplies recognition, and
/// Gate 8 connects it to shared statement dispatch.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ImplStatementIntro<'source> {
    start: usize,
    visibility: Option<VisibilityPrefix<'source>>,
    after_visibility: Option<TriviaRun>,
    impl_keyword: WordSpan<'source>,
    impl_base: usize,
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
    pub(crate) fn body(&self) -> &Recovered<ParsedBindingBody<C>> {
        &self.body
    }
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

impl<C> ParsedBindingBody<C> {
    fn new(range: Range<usize>) -> Self {
        Self {
            range,
            marker: std::marker::PhantomData,
        }
    }
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
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
    let ambient_scope =
        committed.probe(|probe| probe.input().local.push_root_statement_ambient_scope());
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
            StatementIntro::Enum(intro) => {
                let _ = commit_enum_declaration_isolated(&mut committed, intro);
                StatementKind::EnumDeclaration
            }
            StatementIntro::Error(intro) => {
                let _ = commit_error_declaration_isolated(&mut committed, intro);
                StatementKind::ErrorDeclaration
            }
            StatementIntro::Type(intro) => {
                let _ = commit_type_declaration_with_operators(operators, &mut committed, intro);
                StatementKind::TypeDeclaration
            }
            StatementIntro::Role(intro) => {
                let _ = commit_role_declaration_isolated(operators, &mut committed, intro);
                StatementKind::RoleDeclaration
            }
            StatementIntro::Impl(intro) => {
                let _ = commit_impl_declaration_isolated(operators, &mut committed, intro);
                StatementKind::ImplDeclaration
            }
            StatementIntro::Cast(intro) => {
                let _ = commit_cast_declaration_isolated(operators, intro, &mut committed);
                StatementKind::CastDeclaration
            }
            StatementIntro::Act(intro) => {
                let _ = commit_act_declaration_isolated(operators, &mut committed, intro);
                StatementKind::ActDeclaration
            }
            StatementIntro::For(intro) => {
                let _ = commit_for_statement_isolated(operators, &mut committed, intro);
                StatementKind::ForStatement
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
        StatementIntro::Enum(_) => {
            probe.input().rollback(checkpoint);
            return None;
        }
        StatementIntro::Error(_) => {
            probe.input().rollback(checkpoint);
            return None;
        }
        StatementIntro::Type(_) => {
            probe.input().rollback(checkpoint);
            return None;
        }
        StatementIntro::Role(_) => {
            probe.input().rollback(checkpoint);
            return None;
        }
        StatementIntro::Impl(_) => {
            probe.input().rollback(checkpoint);
            return None;
        }
        StatementIntro::Cast(_) => {
            probe.input().rollback(checkpoint);
            return None;
        }
        StatementIntro::Act(_) => {
            probe.input().rollback(checkpoint);
            return None;
        }
        StatementIntro::For(_) => {
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

    if let Some(intro) = i.run(recognize_enum_statement_intro) {
        return Some(StatementIntro::Enum(intro));
    }

    if let Some(intro) = i.run(recognize_error_statement_intro) {
        return Some(StatementIntro::Error(intro));
    }

    if let Some(intro) = i.run(recognize_mod_statement_intro) {
        return Some(StatementIntro::Mod(intro));
    }

    if let Some(intro) = i.run(recognize_type_statement_intro) {
        return Some(StatementIntro::Type(intro));
    }

    if let Some(intro) = i.run(recognize_role_statement_intro) {
        return Some(StatementIntro::Role(intro));
    }

    if let Some(intro) = i.run(recognize_impl_statement_intro) {
        return Some(StatementIntro::Impl(intro));
    }

    if let Some(intro) = i.run(recognize_cast_statement_intro) {
        return Some(StatementIntro::Cast(intro));
    }

    if let Some(intro) = i.run(recognize_act_statement_intro) {
        return Some(StatementIntro::Act(intro));
    }

    if let Some(intro) = i.run(recognize_for_statement_intro) {
        return Some(StatementIntro::For(intro));
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
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
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
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
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

/// Recognizes the sink-free prefix reserved for a standalone Role declaration.
///
/// This remains deliberately separate from `recognize_statement_intro` until
/// the later dispatch gate. An exact `role` keyword establishes declaration
/// authority without probing its mandatory head or body.
#[allow(dead_code)]
fn recognize_role_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<RoleStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let role_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let Some(trivia) = mod_trivia(role_base, &mut i).filter(|trivia| !trivia.is_empty()) else {
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
    if keyword.text() != "role" {
        i.rollback(checkpoint);
        return None;
    }
    Some(RoleStatementIntro {
        start,
        visibility,
        after_visibility,
        role_keyword: keyword,
        role_base,
    })
}

/// Recognizes the sink-free prefix reserved for a standalone Act declaration.
///
/// Unlike the other visibility-prefixed declaration introductions, `my act`
/// preserves Yulang2's local-binding collision. It becomes an Act only when
/// a raw TypeExpression name is visible after the keyword; the lookahead is
/// rolled back so the later head episode owns the same bytes.
#[allow(dead_code)]
fn recognize_act_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ActStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let act_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let Some(trivia) = mod_trivia(act_base, &mut i).filter(|trivia| !trivia.is_empty()) else {
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
    if keyword.text() != "act" {
        i.rollback(checkpoint);
        return None;
    }
    if matches!(
        visibility,
        Some(VisibilityPrefix {
            visibility: Visibility::Private,
            ..
        })
    ) {
        let head_checkpoint = i.checkpoint();
        let head_candidate =
            mod_trivia(act_base, &mut i).is_some() && act_raw_type_head_candidate(&mut i);
        i.rollback(head_checkpoint);
        if !head_candidate {
            i.rollback(checkpoint);
            return None;
        }
    }
    Some(ActStatementIntro {
        start,
        visibility,
        after_visibility,
        act_keyword: keyword,
        act_base,
    })
}

/// Peeks exactly the raw TypeExpression-name forms relevant to ACT-J.
///
/// This deliberately matches `scan_type_name`'s lexical admission without
/// invoking a TypeExpression episode: ordinary words and apostrophe sigils
/// qualify, while `$` and `&` stay outside the current TypeExpression grammar.
fn act_raw_type_head_candidate<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let candidate = i
        .run(scan_path_segment)
        .is_some_and(|name| !matches!(name.text().chars().next(), Some('$' | '&')));
    i.rollback(checkpoint);
    candidate
}

/// Recognizes the sink-free prefix reserved for a standalone Enum declaration.
///
/// `my enum` preserves Yulang2's local-binding collision. It establishes Enum
/// authority only when a raw TypeExpression name is visible after the keyword;
/// the lookahead rolls back so the later header driver owns the same bytes.
#[allow(dead_code)]
fn recognize_enum_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<EnumStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let enum_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let Some(trivia) = mod_trivia(enum_base, &mut i).filter(|trivia| !trivia.is_empty()) else {
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
    if keyword.text() != "enum" {
        i.rollback(checkpoint);
        return None;
    }
    if matches!(
        visibility,
        Some(VisibilityPrefix {
            visibility: Visibility::Private,
            ..
        })
    ) {
        let head_checkpoint = i.checkpoint();
        let head_candidate =
            mod_trivia(enum_base, &mut i).is_some() && enum_raw_type_head_candidate(&mut i);
        i.rollback(head_checkpoint);
        if !head_candidate {
            i.rollback(checkpoint);
            return None;
        }
    }
    Some(EnumStatementIntro {
        start,
        visibility,
        after_visibility,
        enum_keyword: keyword,
        enum_base,
    })
}

/// Peeks the raw TypeExpression-name forms admitted by ENUM-J.
///
/// The shared path-segment scanner accepts ordinary words plus sigil-prefixed
/// forms. Enum accepts only the ordinary and apostrophe forms as raw type
/// heads; `$` and `&` remain outside the current TypeExpression grammar.
fn enum_raw_type_head_candidate<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let candidate = i
        .run(scan_path_segment)
        .is_some_and(|name| !matches!(name.text().chars().next(), Some('$' | '&')));
    i.rollback(checkpoint);
    candidate
}

/// Recognizes the sink-free prefix reserved for a standalone Error declaration.
///
/// `my error` preserves Yulang2's local-binding collision. It establishes
/// Error authority only when a raw TypeExpression name is visible after the
/// keyword; the lookahead rolls back so the later header driver owns the same
/// bytes.
fn recognize_error_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ErrorStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let error_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let Some(trivia) = mod_trivia(error_base, &mut i).filter(|trivia| !trivia.is_empty())
        else {
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
    if keyword.text() != "error" {
        i.rollback(checkpoint);
        return None;
    }
    if matches!(
        visibility,
        Some(VisibilityPrefix {
            visibility: Visibility::Private,
            ..
        })
    ) {
        let head_checkpoint = i.checkpoint();
        let head_candidate =
            mod_trivia(error_base, &mut i).is_some() && error_raw_type_head_candidate(&mut i);
        i.rollback(head_checkpoint);
        if !head_candidate {
            i.rollback(checkpoint);
            return None;
        }
    }
    Some(ErrorStatementIntro {
        start,
        visibility,
        after_visibility,
        error_keyword: keyword,
        error_base,
    })
}

/// Peeks the raw TypeExpression-name forms admitted by ERROR-J.
///
/// The shared path-segment scanner accepts ordinary words plus sigil-prefixed
/// forms. Error accepts only the ordinary and apostrophe forms as raw type
/// heads; `$` and `&` remain outside the current TypeExpression grammar.
fn error_raw_type_head_candidate<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let candidate = i
        .run(scan_path_segment)
        .is_some_and(|name| !matches!(name.text().chars().next(), Some('$' | '&')));
    i.rollback(checkpoint);
    candidate
}

/// Recognizes the sink-free prefix reserved for a standalone Impl declaration.
///
/// This remains deliberately separate from `recognize_statement_intro` until
/// the later dispatch gate. An exact `impl` keyword establishes declaration
/// authority without probing its mandatory head or body.
fn recognize_impl_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ImplStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let impl_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let Some(trivia) = mod_trivia(impl_base, &mut i).filter(|trivia| !trivia.is_empty()) else {
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
    if keyword.text() != "impl" {
        i.rollback(checkpoint);
        return None;
    }
    Some(ImplStatementIntro {
        start,
        visibility,
        after_visibility,
        impl_keyword: keyword,
        impl_base,
    })
}

/// Recognizes the sink-free prefix reserved for a standalone Cast declaration.
///
/// This remains deliberately separate from `recognize_statement_intro` until
/// the later dispatch gate. An exact `cast` keyword establishes declaration
/// authority without probing its mandatory Pattern, target, or body.
#[allow(dead_code)]
fn recognize_cast_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<CastStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let cast_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let Some(trivia) = mod_trivia(cast_base, &mut i).filter(|trivia| !trivia.is_empty()) else {
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
    if keyword.text() != "cast" {
        i.rollback(checkpoint);
        return None;
    }
    Some(CastStatementIntro {
        start,
        visibility,
        after_visibility,
        cast_keyword: keyword,
        cast_base,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ImplTypeExpressionSlot {
    Head,
    Description,
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ImplTailOwner {
    Standalone,
    TypeAttached,
}

/// The sole owner-specific input to the shared post-keyword Impl grammar.
/// Intro recognition, visibility, and the outer declaration node stay with
/// the caller; this spec selects only layout and outer recovery ownership.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ImplTailOwnerSpec {
    owner: ImplTailOwner,
    owner_base: usize,
}

impl ImplTailOwnerSpec {
    fn grammar_role(self, role: ImplRole) -> GrammarRole {
        match self.owner {
            ImplTailOwner::Standalone => GrammarRole::Declaration(DeclarationRole::Impl(role)),
            ImplTailOwner::TypeAttached => GrammarRole::Declaration(DeclarationRole::Type(
                TypeDeclarationRole::AttachedImpl(role),
            )),
        }
    }
}

fn standalone_impl_tail_owner_spec(owner_base: usize) -> ImplTailOwnerSpec {
    ImplTailOwnerSpec {
        owner: ImplTailOwner::Standalone,
        owner_base,
    }
}

/// The isolated owner adapter reserved for a Type-attached Impl tail.
///
/// The baseline remains Type's declaration baseline rather than the column of
/// the later `impl` keyword. Gate 4 supplies the first parsing caller.
#[allow(dead_code)]
fn type_attached_impl_tail_owner_spec(type_base: usize) -> ImplTailOwnerSpec {
    ImplTailOwnerSpec {
        owner: ImplTailOwner::TypeAttached,
        owner_base: type_base,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ImplTypeExpressionEpisodeSpec {
    stops: StopSet,
    scoped_frame: TypeExpressionScopedStopFrame,
    policy: TypeExpressionEpisodePolicy,
    outer_role: GrammarRole,
}

/// One outer Impl TypeExpression slot owns body punctuation only in its
/// logical episode. Nested TypeExpression episodes retain the raw stop bits
/// while the scoped frame suspends their ownership there.
fn impl_type_expression_episode_spec(
    owner_spec: ImplTailOwnerSpec,
    slot: ImplTypeExpressionSlot,
    incoming: StopSet,
    current_episode_depth: usize,
) -> ImplTypeExpressionEpisodeSpec {
    let scoped_stops = StopSet::default()
        .with(StopKind::Colon)
        .with(StopKind::LeftBrace)
        .with(StopKind::Semicolon);
    let stops = incoming
        .with(StopKind::Colon)
        .with(StopKind::LeftBrace)
        .with(StopKind::Semicolon);
    let fresh_primary_locally_owned_stops = match slot {
        ImplTypeExpressionSlot::Head => StopSet::default(),
        ImplTypeExpressionSlot::Description => StopSet::default().with(StopKind::LeftBrace),
    };
    let role = match slot {
        ImplTypeExpressionSlot::Head => ImplRole::Head,
        ImplTypeExpressionSlot::Description => ImplRole::Description,
    };
    ImplTypeExpressionEpisodeSpec {
        stops,
        scoped_frame: TypeExpressionScopedStopFrame {
            stops: scoped_stops,
            visible_episode_depth: current_episode_depth + 1,
        },
        policy: TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops,
            fresh_primary_owns_adjacent_polymorphic_variant_starter: true,
        },
        outer_role: owner_spec.grammar_role(role),
    }
}

fn parse_required_impl_tail_type_expression<'source, E>(
    owner_spec: ImplTailOwnerSpec,
    slot: ImplTypeExpressionSlot,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = impl_type_expression_episode_spec(
        owner_spec,
        slot,
        i.local.stop_set().unwrap_or_default(),
        i.local.type_expression_episode_depth(),
    );
    i.local.push_stop_set(episode.stops);
    i.local
        .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    let parsed = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_outer_missing_role_and_policy(
                    Some(episode.outer_role),
                    episode.policy,
                    i,
                ),
            )
        }))
        .expect("the mandatory Impl TypeExpression entry is total");
    assert_eq!(
        i.local.pop_type_expression_scoped_stop_frame(),
        Some(episode.scoped_frame),
    );
    assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    match parsed {
        Recovered::Complete(parsed) => Recovered::Complete(Box::new(parsed)),
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

fn commit_required_impl_tail_type_expression<'parse, 'source, 'local, E, O>(
    owner_spec: ImplTailOwnerSpec,
    slot: ImplTypeExpressionSlot,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = committed.probe(|probe| {
        let i = probe.input();
        impl_type_expression_episode_spec(
            owner_spec,
            slot,
            i.local.stop_set().unwrap_or_default(),
            i.local.type_expression_episode_depth(),
        )
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(episode.stops);
        i.local
            .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    });
    let parsed = commit_direct_type_expression_with_outer_missing_role_and_policy(
        Some(episode.outer_role),
        episode.policy,
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(
            i.local.pop_type_expression_scoped_stop_frame(),
            Some(episode.scoped_frame),
        );
        assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    });
    let range = parsed.range();
    if range.is_empty() {
        Recovered::Incomplete
    } else {
        Recovered::Complete(range)
    }
}

#[cfg(test)]
fn parse_required_impl_type_expression_isolated<'source, E>(
    slot: ImplTypeExpressionSlot,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_required_impl_tail_type_expression(standalone_impl_tail_owner_spec(0), slot, i)
}

#[cfg(test)]
fn commit_required_impl_type_expression_isolated<'parse, 'source, 'local, E, O>(
    slot: ImplTypeExpressionSlot,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_required_impl_tail_type_expression(standalone_impl_tail_owner_spec(0), slot, committed)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RoleHeadTypeExpressionEpisodeSpec {
    stops: StopSet,
    scoped_frame: TypeExpressionScopedStopFrame,
    policy: TypeExpressionEpisodePolicy,
    outer_role: GrammarRole,
}

/// One outer Role head owns body punctuation only in its logical
/// TypeExpression episode. Recursive TypeExpression episodes retain the raw
/// stop bits while the scoped frame suspends Role's authority there.
fn role_head_type_expression_episode_spec(
    incoming: StopSet,
    current_episode_depth: usize,
) -> RoleHeadTypeExpressionEpisodeSpec {
    let scoped_stops = StopSet::default()
        .with(StopKind::Colon)
        .with(StopKind::LeftBrace)
        .with(StopKind::Semicolon);
    RoleHeadTypeExpressionEpisodeSpec {
        stops: incoming
            .with(StopKind::Colon)
            .with(StopKind::LeftBrace)
            .with(StopKind::Semicolon),
        scoped_frame: TypeExpressionScopedStopFrame {
            stops: scoped_stops,
            visible_episode_depth: current_episode_depth + 1,
        },
        policy: TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops: StopSet::default(),
            fresh_primary_owns_adjacent_polymorphic_variant_starter: true,
        },
        outer_role: GrammarRole::Declaration(DeclarationRole::Role(
            crate::session::RoleDeclarationRole::Head,
        )),
    }
}

fn parse_required_role_head_type_expression_isolated<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = role_head_type_expression_episode_spec(
        i.local.stop_set().unwrap_or_default(),
        i.local.type_expression_episode_depth(),
    );
    i.local.push_stop_set(episode.stops);
    i.local
        .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    let parsed = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_outer_missing_role_and_policy(
                    Some(episode.outer_role),
                    episode.policy,
                    i,
                ),
            )
        }))
        .expect("the mandatory Role head TypeExpression entry is total");
    assert_eq!(
        i.local.pop_type_expression_scoped_stop_frame(),
        Some(episode.scoped_frame),
    );
    assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    match parsed {
        Recovered::Complete(parsed) => Recovered::Complete(Box::new(parsed)),
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

fn commit_required_role_head_type_expression_isolated<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = committed.probe(|probe| {
        let i = probe.input();
        role_head_type_expression_episode_spec(
            i.local.stop_set().unwrap_or_default(),
            i.local.type_expression_episode_depth(),
        )
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(episode.stops);
        i.local
            .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    });
    let parsed = commit_direct_type_expression_with_outer_missing_role_and_policy(
        Some(episode.outer_role),
        episode.policy,
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(
            i.local.pop_type_expression_scoped_stop_frame(),
            Some(episode.scoped_frame),
        );
        assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    });
    let range = parsed.range();
    if range.is_empty() {
        Recovered::Incomplete
    } else {
        Recovered::Complete(range)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ActTypeExpressionSlot {
    Head,
    Source,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ActTypeExpressionEpisodeSpec {
    stops: StopSet,
    scoped_frame: TypeExpressionScopedStopFrame,
    policy: TypeExpressionEpisodePolicy,
    outer_role: GrammarRole,
}

/// One outer Act head owns its source/body punctuation only in its logical
/// TypeExpression episode. Recursive TypeExpression episodes retain the raw
/// stop bits while the scoped frame suspends Act's authority there.
fn act_type_expression_episode_spec(
    slot: ActTypeExpressionSlot,
    incoming: StopSet,
    current_episode_depth: usize,
) -> ActTypeExpressionEpisodeSpec {
    let scoped_stops = match slot {
        ActTypeExpressionSlot::Head => StopSet::default().with(StopKind::Equal),
        ActTypeExpressionSlot::Source => StopSet::default(),
    }
    .with(StopKind::Colon)
    .with(StopKind::LeftBrace)
    .with(StopKind::Semicolon)
    .with(StopKind::Derives);
    let stops = match slot {
        ActTypeExpressionSlot::Head => incoming.with(StopKind::Equal),
        ActTypeExpressionSlot::Source => incoming,
    }
    .with(StopKind::Colon)
    .with(StopKind::LeftBrace)
    .with(StopKind::Semicolon)
    .with(StopKind::Derives);
    let act_role = match slot {
        ActTypeExpressionSlot::Head => crate::session::ActDeclarationRole::Head,
        ActTypeExpressionSlot::Source => crate::session::ActDeclarationRole::Source,
    };
    ActTypeExpressionEpisodeSpec {
        stops,
        scoped_frame: TypeExpressionScopedStopFrame {
            stops: scoped_stops,
            visible_episode_depth: current_episode_depth + 1,
        },
        policy: TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops: StopSet::default().with(StopKind::Derives),
            fresh_primary_owns_adjacent_polymorphic_variant_starter: true,
        },
        outer_role: GrammarRole::Declaration(DeclarationRole::Act(act_role)),
    }
}

fn parse_required_act_head_type_expression_isolated<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = act_type_expression_episode_spec(
        ActTypeExpressionSlot::Head,
        i.local.stop_set().unwrap_or_default(),
        i.local.type_expression_episode_depth(),
    );
    i.local.push_stop_set(episode.stops);
    i.local
        .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    let parsed = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_outer_missing_role_and_policy(
                    Some(episode.outer_role),
                    episode.policy,
                    i,
                ),
            )
        }))
        .expect("the mandatory Act head TypeExpression entry is total");
    assert_eq!(
        i.local.pop_type_expression_scoped_stop_frame(),
        Some(episode.scoped_frame),
    );
    assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    match parsed {
        Recovered::Complete(parsed) => Recovered::Complete(Box::new(parsed)),
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

fn commit_required_act_head_type_expression_isolated<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = committed.probe(|probe| {
        let i = probe.input();
        act_type_expression_episode_spec(
            ActTypeExpressionSlot::Head,
            i.local.stop_set().unwrap_or_default(),
            i.local.type_expression_episode_depth(),
        )
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(episode.stops);
        i.local
            .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    });
    let parsed = commit_direct_type_expression_with_outer_missing_role_and_policy(
        Some(episode.outer_role),
        episode.policy,
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(
            i.local.pop_type_expression_scoped_stop_frame(),
            Some(episode.scoped_frame),
        );
        assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    });
    let range = parsed.range();
    if range.is_empty() {
        Recovered::Incomplete
    } else {
        Recovered::Complete(range)
    }
}

fn parse_required_act_source_type_expression_isolated<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = act_type_expression_episode_spec(
        ActTypeExpressionSlot::Source,
        i.local.stop_set().unwrap_or_default(),
        i.local.type_expression_episode_depth(),
    );
    i.local.push_stop_set(episode.stops);
    i.local
        .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    let parsed = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_outer_missing_role_and_policy(
                    Some(episode.outer_role),
                    episode.policy,
                    i,
                ),
            )
        }))
        .expect("the mandatory Act source TypeExpression entry is total");
    assert_eq!(
        i.local.pop_type_expression_scoped_stop_frame(),
        Some(episode.scoped_frame),
    );
    assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    match parsed {
        Recovered::Complete(parsed) => Recovered::Complete(Box::new(parsed)),
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

fn commit_required_act_source_type_expression_isolated<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = committed.probe(|probe| {
        let i = probe.input();
        act_type_expression_episode_spec(
            ActTypeExpressionSlot::Source,
            i.local.stop_set().unwrap_or_default(),
            i.local.type_expression_episode_depth(),
        )
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(episode.stops);
        i.local
            .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    });
    let parsed = commit_direct_type_expression_with_outer_missing_role_and_policy(
        Some(episode.outer_role),
        episode.policy,
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(
            i.local.pop_type_expression_scoped_stop_frame(),
            Some(episode.scoped_frame),
        );
        assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    });
    let range = parsed.range();
    if range.is_empty() {
        Recovered::Incomplete
    } else {
        Recovered::Complete(range)
    }
}

/// Parses an optional Act copy source after the completed or recovered head.
/// A non-equals tail is rolled back intact for Gate 5's body-form judge.
fn parse_act_source_clause_after_head_isolated<'source, E>(
    act_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<ActSourceClause<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return None;
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(act_base, i) else {
        i.rollback(checkpoint);
        return None;
    };
    let Some(equals) = i.run(scan_declaration_exact_equals) else {
        i.rollback(checkpoint);
        return None;
    };
    let source_gap = i.checkpoint();
    let source = if mod_trivia(act_base, i).is_some() {
        parse_required_act_source_type_expression_isolated(i)
    } else {
        i.rollback(source_gap);
        parse_required_act_source_type_expression_isolated(i)
    };
    let end = match &source {
        Recovered::Complete(source) => source.range().end,
        Recovered::Incomplete => equals.end,
    };
    Some(ActSourceClause {
        equals: equals.clone(),
        source,
        range: equals.start..end,
    })
}

/// Direct-CST counterpart of [`parse_act_source_clause_after_head_isolated`].
/// It emits only actual head/source gaps and the equals token; an absent
/// equals leaves the full original tail untouched for Gate 5.
#[derive(Clone, Debug, Eq, PartialEq)]
struct CommittedActSourceClause {
    equals: Range<usize>,
    source: Recovered<Range<usize>>,
    range: Range<usize>,
}

fn commit_act_source_clause_after_head_isolated<'parse, 'source, 'local, E, O>(
    act_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<CommittedActSourceClause>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let equals = committed.probe(|probe| {
        let i = probe.input();
        if any_ambient_owner_claims(i) {
            return None;
        }
        let checkpoint = i.checkpoint();
        let equals = mod_trivia(act_base, i).and_then(|_| i.run(scan_declaration_exact_equals));
        i.rollback(checkpoint);
        equals
    })?;
    let head_gap = committed
        .probe(|probe| mod_trivia(act_base, probe.input()))
        .expect("the committed Act equals was already classified");
    committed.emit_trivia(&head_gap);
    let actual_equals = committed
        .probe(|probe| probe.input().run(scan_declaration_exact_equals))
        .expect("the committed Act equals remains at the cursor");
    debug_assert_eq!(actual_equals, equals);
    committed.token(SyntaxKind::Equals, actual_equals.clone());

    let source_gap = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let trivia = mod_trivia(act_base, i);
        i.rollback(checkpoint);
        trivia
    });
    if let Some(source_gap) = source_gap {
        let consumed = committed
            .probe(|probe| mod_trivia(act_base, probe.input()))
            .expect("the committed Act source gap was already classified");
        assert_eq!(consumed.range(), source_gap.range());
        committed.emit_trivia(&consumed);
    }
    let source = commit_required_act_source_type_expression_isolated(committed);
    let end = match &source {
        Recovered::Complete(range) => range.end,
        Recovered::Incomplete => actual_equals.end,
    };
    Some(CommittedActSourceClause {
        equals: actual_equals.clone(),
        source,
        range: actual_equals.start..end,
    })
}

/// Parses one accepted Act continuation without making Act reachable from
/// the public statement dispatcher. The Head/Source slots and the body-form
/// judge remain distinct after Gate 10's atomic promotion.
pub(crate) fn parse_act_declaration_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ActDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let declaration = (|| {
        let intro = i.run(recognize_act_statement_intro)?;
        let visibility = intro
            .visibility
            .map_or(Visibility::Private, |prefix| prefix.visibility);
        let head = if any_ambient_owner_claims(&mut i) {
            Recovered::Incomplete
        } else {
            let checkpoint = i.checkpoint();
            if mod_trivia(intro.act_base, &mut i).is_some() {
                parse_required_act_head_type_expression_isolated(&mut i)
            } else {
                i.rollback(checkpoint);
                Recovered::Incomplete
            }
        };
        let mut derives = matches!(head, Recovered::Complete(_))
            .then(|| {
                recognize_derives_attachment_start(
                    DerivesAttachmentOwner::Act,
                    DerivesAttachmentPosition::Header,
                    intro.act_base,
                    &mut i,
                )
                .map(|start| parse_derives_attachments_isolated(start, &mut i))
                .unwrap_or_default()
            })
            .unwrap_or_default();
        let source = parse_act_source_clause_after_head_isolated(intro.act_base, &mut i);
        if source
            .as_ref()
            .is_some_and(|clause| matches!(clause.source, Recovered::Complete(_)))
        {
            if let Some(start) = recognize_derives_attachment_start(
                DerivesAttachmentOwner::Act,
                DerivesAttachmentPosition::Header,
                intro.act_base,
                &mut i,
            ) {
                derives.extend(parse_derives_attachments_isolated(start, &mut i));
            }
        }
        let head_and_source_complete = matches!(head, Recovered::Complete(_))
            && source
                .as_ref()
                .is_none_or(|clause| matches!(clause.source, Recovered::Complete(_)));
        let body = parse_act_body_ast(table, intro.act_base, head_and_source_complete, &mut i);
        if act_body_has_actual_trailing_close(&body) {
            if let Some(start) = recognize_derives_attachment_start(
                DerivesAttachmentOwner::Act,
                DerivesAttachmentPosition::Trailing,
                intro.act_base,
                &mut i,
            ) {
                derives.extend(parse_derives_attachments_isolated(start, &mut i));
            }
        }
        let end = i.pos();
        Some(ActDeclaration {
            visibility,
            head,
            source,
            derives,
            body,
            range: intro.start..end,
        })
    })();
    i.errors_rollback(errors_checkpoint);
    declaration
}

fn parse_act_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    act_base: usize,
    head_and_source_complete: bool,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<ActBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return head_and_source_complete
            .then_some(ActBody::Bodyless { semicolon: None })
            .map_or(Recovered::Incomplete, Recovered::Complete);
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(act_base, i) else {
        i.rollback(checkpoint);
        if head_and_source_complete && act_body_implicit_boundary_pending(act_base, i) {
            return Recovered::Complete(ActBody::Bodyless { semicolon: None });
        }
        return Recovered::Incomplete;
    };
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        if head_and_source_complete && act_body_implicit_boundary_pending(act_base, i) {
            return Recovered::Complete(ActBody::Bodyless { semicolon: None });
        }
        if act_body_introducer_error_retry_ast(act_base, i).is_some_and(|retry| retry) {
            return parse_act_body_ast(table, act_base, head_and_source_complete, i);
        }
        return Recovered::Incomplete;
    };
    match punctuation.kind() {
        PunctuationKind::Semicolon => Recovered::Complete(ActBody::Bodyless {
            semicolon: Some(punctuation.range()),
        }),
        PunctuationKind::Open(Delimiter::Brace) => Recovered::Complete(ActBody::Braced {
            block: parse_braced_statement_block_expression(table, punctuation.range(), i),
        }),
        PunctuationKind::Colon => Recovered::Complete(ActBody::Colon {
            colon: punctuation.range(),
            body: parse_act_colon_body_ast(table, act_base, i)
                .map_or(Recovered::Incomplete, Recovered::Complete),
        }),
        _ => {
            i.rollback(checkpoint);
            if head_and_source_complete && act_body_implicit_boundary_pending(act_base, i) {
                return Recovered::Complete(ActBody::Bodyless { semicolon: None });
            }
            if act_body_introducer_error_retry_ast(act_base, i).is_some_and(|retry| retry) {
                parse_act_body_ast(table, act_base, head_and_source_complete, i)
            } else {
                Recovered::Incomplete
            }
        }
    }
}

fn parse_act_colon_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    act_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<ActColonBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia)?;
    if i.input.source()[trivia.range()].contains(['\r', '\n']) {
        if i.local.line().line_indent <= act_base {
            i.rollback(checkpoint);
            return None;
        }
        let block_indent = i.local.line().line_indent;
        return Some(ActColonBody::Indented {
            block: parse_indented_act_body(table, trivia, act_base, block_indent, i),
        });
    }
    let ambient_scope = i.local.push_inline_canonical_statement_ambient_scope(
        crate::session::InlineStatementOwnerKind::ActColonBody,
    );
    let statement = i
        .run(from_fn(|i| parse_canonical_statement(table, i)))
        .or_else(|| {
            act_body_error_retry_ast(table, i)
                .is_some_and(|retry| retry)
                .then(|| i.run(from_fn(|i| parse_canonical_statement(table, i))))
                .flatten()
        });
    let body = statement.map(|statement| {
        let terminal = i.checkpoint();
        if i.run(scan_punctuation)
            .is_none_or(|punctuation| punctuation.kind() != PunctuationKind::Semicolon)
        {
            i.rollback(terminal);
        }
        ActColonBody::Inline {
            statement: Box::new(statement),
        }
    });
    assert_eq!(i.local.pop_ambient_owner_scope(), Some(ambient_scope));
    body
}

fn act_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Semicolon
                | PunctuationKind::Open(Delimiter::Brace)
                | PunctuationKind::Colon
        )
    });
    i.rollback(checkpoint);
    pending
}

/// Tests an Act tail without consuming it. Unlike Role's mandatory body,
/// this recognizes the caller-owned boundary that completes tail-nothing.
fn act_body_implicit_boundary_pending<E>(act_base: usize, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) || i.input.remainder().is_empty() {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = match mod_trivia(act_base, i) {
        None => i
            .run(scan_trivia)
            .is_some_and(|trivia| i.input.source()[trivia.range()].contains(['\r', '\n'])),
        Some(_) if i.input.remainder().is_empty() => true,
        Some(_) => i.run(scan_punctuation).is_some_and(|punctuation| {
            matches!(
                punctuation.kind(),
                PunctuationKind::Comma
                    | PunctuationKind::Close(
                        Delimiter::Parenthesis | Delimiter::Bracket | Delimiter::Brace
                    )
            )
        }),
    };
    i.rollback(checkpoint);
    pending
}

fn act_colon_body_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Semicolon
                | PunctuationKind::Comma
                | PunctuationKind::Close(
                    Delimiter::Parenthesis | Delimiter::Bracket | Delimiter::Brace
                )
        )
    });
    i.rollback(checkpoint);
    pending
}

/// AST half of the one maximal Act body-introducer invalid run. Direct-CST
/// emission is intentionally left to Gate 6; this only preserves the same
/// starter and boundary ownership for the AST adapter.
fn act_body_introducer_error_retry_ast<'source, E>(
    act_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if act_body_starter_pending(i) {
            return (start < i.pos()).then_some(true);
        }
        if act_body_implicit_boundary_pending(act_base, i) {
            return (start < i.pos()).then_some(false);
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < i.pos()).then_some(false);
        };
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn act_body_error_retry_ast<'source, E>(
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
        if act_colon_body_boundary_pending(i) {
            return (start < i.pos()).then_some(false);
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < i.pos()).then_some(false);
        };
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        let checkpoint = i.checkpoint();
        let candidate = i
            .run(from_fn(|i| parse_canonical_statement(table, i)))
            .is_some();
        i.rollback(checkpoint);
        if candidate {
            return Some(true);
        }
    }
}

/// Direct-CST counterpart of [`parse_act_declaration_isolated`]. Gate 10
/// promotes this exact adapter into shared statement dispatch.
pub(crate) fn commit_act_declaration_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: ActStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    committed.start_node(SyntaxKind::ActDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::ActKw, intro.act_keyword.range());

    let head_terminated_incomplete = if committed
        .probe(|probe| any_ambient_owner_claims(probe.input()))
    {
        true
    } else if let Some(trivia) = committed.probe(|probe| mod_trivia(intro.act_base, probe.input()))
    {
        committed.emit_trivia(&trivia);
        matches!(
            commit_required_act_head_type_expression_isolated(committed),
            Recovered::Incomplete
        )
    } else {
        true
    };
    if !head_terminated_incomplete {
        if let Some(start) = committed.probe(|probe| {
            recognize_derives_attachment_start(
                DerivesAttachmentOwner::Act,
                DerivesAttachmentPosition::Header,
                intro.act_base,
                probe.input(),
            )
        }) {
            let _ = commit_derives_attachments_isolated(start, committed);
        }
    }
    let source = commit_act_source_clause_after_head_isolated(intro.act_base, committed);
    let source_terminated_incomplete = source
        .as_ref()
        .is_some_and(|source| matches!(source.source, Recovered::Incomplete));
    if source
        .as_ref()
        .is_some_and(|source| matches!(source.source, Recovered::Complete(_)))
    {
        if let Some(start) = committed.probe(|probe| {
            recognize_derives_attachment_start(
                DerivesAttachmentOwner::Act,
                DerivesAttachmentPosition::Header,
                intro.act_base,
                probe.input(),
            )
        }) {
            let _ = commit_derives_attachments_isolated(start, committed);
        }
    }
    let has_actual_braced_close = commit_act_body_isolated(
        table,
        intro.act_base,
        !head_terminated_incomplete && !source_terminated_incomplete,
        committed,
    );
    if has_actual_braced_close {
        if let Some(start) = committed.probe(|probe| {
            recognize_derives_attachment_start(
                DerivesAttachmentOwner::Act,
                DerivesAttachmentPosition::Trailing,
                intro.act_base,
                probe.input(),
            )
        }) {
            let _ = commit_derives_attachments_isolated(start, committed);
        }
    }
    let end = committed_position(committed);
    committed.finish_node();
    committed.probe(|probe| probe.input().errors_rollback(errors_checkpoint));
    Recovered::Complete(intro.start..end)
}

#[derive(Clone)]
enum ActBodyStarter {
    Bodyless(Range<usize>),
    Braced(Range<usize>),
    Colon(Range<usize>),
}

fn commit_act_body_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    act_base: usize,
    head_and_source_complete: bool,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        return false;
    }
    let starter = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let starter = mod_trivia(act_base, i).and_then(|trivia| {
            let punctuation = i.run(scan_punctuation)?;
            let starter = match punctuation.kind() {
                PunctuationKind::Semicolon => ActBodyStarter::Bodyless(punctuation.range()),
                PunctuationKind::Open(Delimiter::Brace) => {
                    ActBodyStarter::Braced(punctuation.range())
                }
                PunctuationKind::Colon => ActBodyStarter::Colon(punctuation.range()),
                _ => return None,
            };
            Some((trivia, starter))
        });
        i.rollback(checkpoint);
        starter
    });
    let Some((trivia, starter)) = starter else {
        if head_and_source_complete
            && committed.probe(|probe| act_body_implicit_boundary_pending(act_base, probe.input()))
        {
            // Tail-nothing is a completed body form. It deliberately emits
            // neither a recovery node nor a synthetic semicolon/token.
            return false;
        }
        let trivia = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let trivia = mod_trivia(act_base, i);
            i.rollback(checkpoint);
            trivia
        });
        let Some(trivia) = trivia else {
            if !head_and_source_complete {
                return false;
            }
            emit_act_body_introducer_missing(committed);
            return false;
        };
        let newline = committed
            .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
        if newline {
            if !head_and_source_complete {
                return false;
            }
            emit_act_body_introducer_missing(committed);
            return false;
        }
        let consumed_trivia = committed
            .probe(|probe| mod_trivia(act_base, probe.input()))
            .expect("the Act body-introducer recovery leaves its leading trivia at the cursor");
        assert_eq!(consumed_trivia.range(), trivia.range());
        committed.emit_trivia(&consumed_trivia);
        match act_body_introducer_error_retry(act_base, committed) {
            Some(true) => {
                return commit_act_body_isolated(
                    table,
                    act_base,
                    head_and_source_complete,
                    committed,
                );
            }
            Some(false) => {}
            None if head_and_source_complete => emit_act_body_introducer_missing(committed),
            None => {}
        }
        return false;
    };

    let consumed_trivia = committed
        .probe(|probe| mod_trivia(act_base, probe.input()))
        .expect("the accepted Act body starter leaves its leading trivia at the cursor");
    assert_eq!(consumed_trivia.range(), trivia.range());
    committed.emit_trivia(&consumed_trivia);
    let punctuation = committed
        .probe(|probe| probe.input().run(scan_punctuation))
        .expect("the accepted Act body starter remains at the cursor");
    match starter {
        ActBodyStarter::Bodyless(range) => {
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Semicolon, range);
            false
        }
        ActBodyStarter::Braced(range) => {
            assert_eq!(punctuation.range(), range);
            commit_braced_statement_block_expression(table, range, committed);
            committed_act_body_has_actual_trailing_close(committed)
        }
        ActBodyStarter::Colon(range) => {
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Colon, range);
            commit_act_colon_body_isolated(table, act_base, committed);
            false
        }
    }
}

fn committed_act_body_has_actual_trailing_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| {
        let i = probe.input();
        i.pos() > 0 && i.input.source().as_bytes().get(i.pos() - 1) == Some(&b'}')
    })
}

fn commit_act_colon_body_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    act_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    let trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia scan is total");
    let newline = committed
        .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
    if newline && committed.probe(|probe| probe.input().local.line().line_indent <= act_base) {
        committed.probe(|probe| probe.input().rollback(checkpoint));
        emit_act_body_missing(committed);
        return;
    }
    if newline {
        let block_indent = committed.probe(|probe| probe.input().local.line().line_indent);
        commit_indented_act_body(table, trivia, act_base, block_indent, committed);
        return;
    }
    committed.emit_trivia(&trivia);
    let ambient_scope = committed.probe(|probe| {
        probe
            .input()
            .local
            .push_inline_canonical_statement_ambient_scope(
                crate::session::InlineStatementOwnerKind::ActColonBody,
            )
    });
    let statement_committed = if commit_canonical_statement(table, LeadingTrivia::None, committed) {
        true
    } else {
        match act_body_error_retry(table, committed) {
            Some(true) => commit_canonical_statement(table, LeadingTrivia::None, committed),
            Some(false) => false,
            None => {
                emit_act_body_missing(committed);
                false
            }
        }
    };
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

fn act_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
    act_base: usize,
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
        loop {
            let i = probe.input();
            if act_body_starter_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), true));
            }
            if act_body_implicit_boundary_pending(act_base, i) {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            let character = i.input.remainder().chars().next()?;
            if matches!(character, '\r' | '\n') {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            i.input.next()?;
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    })?;
    emit_act_error(
        committed,
        crate::session::ActDeclarationRole::BodyIntroducer,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
        recovered.0,
    );
    Some(recovered.1)
}

fn act_body_error_retry<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
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
        loop {
            {
                let i = probe.input();
                if act_colon_body_boundary_pending(i) {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                }
                let character = i.input.remainder().chars().next()?;
                if matches!(character, '\r' | '\n') {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                }
                i.input.next()?;
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            if crate::grammar::expression::direct_canonical_statement_candidate(
                table,
                LeadingTrivia::None,
                probe,
            ) {
                let end = probe.input().pos();
                return Some((start..end, true));
            }
        }
    })?;
    emit_act_error(
        committed,
        crate::session::ActDeclarationRole::Body,
        ExpectedSyntax::Statement,
        recovered.0,
    );
    Some(recovered.1)
}

/// Parses one accepted Role continuation without making Role reachable from
/// the public statement dispatcher.  The prefix, head episode, and body
/// punctuation each retain their own authority so Gate 9 can promote this
/// exact adapter atomically.
pub(crate) fn parse_role_declaration_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<RoleDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let declaration = (|| {
        let intro = i.run(recognize_role_statement_intro)?;
        let visibility = intro
            .visibility
            .map_or(Visibility::Private, |prefix| prefix.visibility);
        let head = if any_ambient_owner_claims(&mut i) {
            Recovered::Incomplete
        } else {
            let checkpoint = i.checkpoint();
            if mod_trivia(intro.role_base, &mut i).is_some() {
                parse_required_role_head_type_expression_isolated(&mut i)
            } else {
                i.rollback(checkpoint);
                Recovered::Incomplete
            }
        };
        let body = parse_role_body_ast(table, intro.role_base, &mut i);
        let end = i.pos();
        Some(RoleDeclaration {
            visibility,
            head,
            body,
            range: intro.start..end,
        })
    })();
    i.errors_rollback(errors_checkpoint);
    declaration
}

fn parse_role_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    role_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<RoleBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return Recovered::Incomplete;
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(role_base, i) else {
        i.rollback(checkpoint);
        return Recovered::Incomplete;
    };
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        if role_body_introducer_error_retry_ast(i).is_some_and(|retry| retry) {
            return parse_role_body_ast(table, role_base, i);
        }
        return Recovered::Incomplete;
    };
    match punctuation.kind() {
        PunctuationKind::Semicolon => Recovered::Complete(RoleBody::Bodyless {
            semicolon: punctuation.range(),
        }),
        PunctuationKind::Open(Delimiter::Brace) => Recovered::Complete(RoleBody::Braced {
            block: parse_braced_statement_block_expression(table, punctuation.range(), i),
        }),
        PunctuationKind::Colon => Recovered::Complete(RoleBody::Colon {
            colon: punctuation.range(),
            body: parse_role_colon_body_ast(table, role_base, i)
                .map_or(Recovered::Incomplete, Recovered::Complete),
        }),
        _ => {
            i.rollback(checkpoint);
            if role_body_introducer_error_retry_ast(i).is_some_and(|retry| retry) {
                parse_role_body_ast(table, role_base, i)
            } else {
                Recovered::Incomplete
            }
        }
    }
}

fn parse_role_colon_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    role_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<RoleColonBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia)?;
    if i.input.source()[trivia.range()].contains(['\r', '\n']) {
        if i.local.line().line_indent <= role_base {
            i.rollback(checkpoint);
            return None;
        }
        let block_indent = i.local.line().line_indent;
        return Some(RoleColonBody::Indented {
            block: parse_indented_role_body(table, trivia, role_base, block_indent, i),
        });
    }
    let ambient_scope = i.local.push_inline_canonical_statement_ambient_scope(
        crate::session::InlineStatementOwnerKind::RoleColonBody,
    );
    let statement = i
        .run(from_fn(|i| parse_canonical_statement(table, i)))
        .or_else(|| {
            role_body_error_retry_ast(table, i)
                .is_some_and(|retry| retry)
                .then(|| i.run(from_fn(|i| parse_canonical_statement(table, i))))
                .flatten()
        });
    let body = statement.map(|statement| {
        let terminal = i.checkpoint();
        if i.run(scan_punctuation)
            .is_none_or(|punctuation| punctuation.kind() != PunctuationKind::Semicolon)
        {
            i.rollback(terminal);
        }
        RoleColonBody::Inline {
            statement: Box::new(statement),
        }
    });
    assert_eq!(i.local.pop_ambient_owner_scope(), Some(ambient_scope));
    body
}

fn role_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Semicolon
                | PunctuationKind::Open(Delimiter::Brace)
                | PunctuationKind::Colon
        )
    });
    i.rollback(checkpoint);
    pending
}

fn role_body_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Comma
                | PunctuationKind::Close(
                    Delimiter::Parenthesis | Delimiter::Bracket | Delimiter::Brace
                )
                | PunctuationKind::Open(Delimiter::Brace)
                | PunctuationKind::Colon
                | PunctuationKind::Semicolon
        )
    });
    i.rollback(checkpoint);
    pending
}

/// AST half of the one maximal Role body-introducer invalid run.  The direct
/// emission is deliberately deferred to Gate 5, but starter/boundary input
/// ownership already matches that future committed path.
fn role_body_introducer_error_retry_ast<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if role_body_starter_pending(i) {
            return (start < i.pos()).then_some(true);
        }
        if role_body_boundary_pending(i) {
            return (start < i.pos()).then_some(false);
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < i.pos()).then_some(false);
        };
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn role_body_error_retry_ast<'source, E>(
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
        if role_body_boundary_pending(i) {
            return (start < i.pos()).then_some(false);
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < i.pos()).then_some(false);
        };
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        let checkpoint = i.checkpoint();
        let candidate = i
            .run(from_fn(|i| parse_canonical_statement(table, i)))
            .is_some();
        i.rollback(checkpoint);
        if candidate {
            return Some(true);
        }
    }
}

/// Direct-CST counterpart of [`parse_role_declaration_isolated`].  Like the
/// AST adapter, it remains deliberately outside statement dispatch until the
/// Gate 9 atomic promotion.
pub(crate) fn commit_role_declaration_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: RoleStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    committed.start_node(SyntaxKind::RoleDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::RoleKw, intro.role_keyword.range());

    let head_terminated_incomplete = if committed
        .probe(|probe| any_ambient_owner_claims(probe.input()))
    {
        true
    } else if let Some(trivia) = committed.probe(|probe| mod_trivia(intro.role_base, probe.input()))
    {
        committed.emit_trivia(&trivia);
        matches!(
            commit_required_role_head_type_expression_isolated(committed),
            Recovered::Incomplete
        )
    } else {
        true
    };

    commit_role_body_isolated(
        table,
        intro.role_base,
        committed,
        head_terminated_incomplete,
    );
    let end = committed_position(committed);
    committed.finish_node();
    committed.probe(|probe| probe.input().errors_rollback(errors_checkpoint));
    Recovered::Complete(intro.start..end)
}

#[derive(Clone)]
enum RoleBodyStarter {
    Bodyless(Range<usize>),
    Braced(Range<usize>),
    Colon(Range<usize>),
}

fn commit_role_body_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    role_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    head_terminated_incomplete: bool,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        return;
    }
    let starter = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let starter = mod_trivia(role_base, i).and_then(|trivia| {
            let punctuation = i.run(scan_punctuation)?;
            let starter = match punctuation.kind() {
                PunctuationKind::Semicolon => RoleBodyStarter::Bodyless(punctuation.range()),
                PunctuationKind::Open(Delimiter::Brace) => {
                    RoleBodyStarter::Braced(punctuation.range())
                }
                PunctuationKind::Colon => RoleBodyStarter::Colon(punctuation.range()),
                _ => return None,
            };
            Some((trivia, starter))
        });
        i.rollback(checkpoint);
        starter
    });
    let Some((trivia, starter)) = starter else {
        let trivia = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let trivia = mod_trivia(role_base, i);
            i.rollback(checkpoint);
            trivia
        });
        let Some(trivia) = trivia else {
            if !head_terminated_incomplete {
                emit_role_body_introducer_missing(committed);
            }
            return;
        };
        let newline = committed
            .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
        if newline {
            if !head_terminated_incomplete {
                emit_role_body_introducer_missing(committed);
            }
            return;
        }
        let consumed_trivia = committed
            .probe(|probe| mod_trivia(role_base, probe.input()))
            .expect("the Role body-introducer recovery leaves its leading trivia at the cursor");
        assert_eq!(consumed_trivia.range(), trivia.range());
        committed.emit_trivia(&consumed_trivia);
        match role_body_introducer_error_retry(committed) {
            Some(true) => {
                commit_role_body_isolated(table, role_base, committed, head_terminated_incomplete);
            }
            Some(false) => {}
            None if !head_terminated_incomplete => emit_role_body_introducer_missing(committed),
            None => {}
        }
        return;
    };

    let consumed_trivia = committed
        .probe(|probe| mod_trivia(role_base, probe.input()))
        .expect("the accepted Role body starter leaves its leading trivia at the cursor");
    assert_eq!(consumed_trivia.range(), trivia.range());
    committed.emit_trivia(&consumed_trivia);
    let punctuation = committed
        .probe(|probe| probe.input().run(scan_punctuation))
        .expect("the accepted Role body starter remains at the cursor");
    match starter {
        RoleBodyStarter::Bodyless(range) => {
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Semicolon, range);
        }
        RoleBodyStarter::Braced(range) => {
            assert_eq!(punctuation.range(), range);
            commit_braced_statement_block_expression(table, range, committed);
        }
        RoleBodyStarter::Colon(range) => {
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Colon, range);
            commit_role_colon_body_isolated(table, role_base, committed);
        }
    }
}

fn commit_role_colon_body_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    role_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    let trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia scan is total");
    let newline = committed
        .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
    if newline && committed.probe(|probe| probe.input().local.line().line_indent <= role_base) {
        committed.probe(|probe| probe.input().rollback(checkpoint));
        emit_role_body_missing(committed);
        return;
    }
    if newline {
        let block_indent = committed.probe(|probe| probe.input().local.line().line_indent);
        commit_indented_role_body(table, trivia, role_base, block_indent, committed);
        return;
    }
    committed.emit_trivia(&trivia);
    let ambient_scope = committed.probe(|probe| {
        probe
            .input()
            .local
            .push_inline_canonical_statement_ambient_scope(
                crate::session::InlineStatementOwnerKind::RoleColonBody,
            )
    });
    let statement_committed = if commit_canonical_statement(table, LeadingTrivia::None, committed) {
        true
    } else {
        match role_body_error_retry(table, committed) {
            Some(true) => commit_canonical_statement(table, LeadingTrivia::None, committed),
            Some(false) => false,
            None => {
                emit_role_body_missing(committed);
                false
            }
        }
    };
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

fn role_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
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
        loop {
            let i = probe.input();
            if role_body_starter_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), true));
            }
            if role_body_boundary_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            let character = i.input.remainder().chars().next()?;
            if matches!(character, '\r' | '\n') {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            i.input.next()?;
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    })?;
    emit_role_error(
        committed,
        crate::session::RoleDeclarationRole::BodyIntroducer,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
        recovered.0,
    );
    Some(recovered.1)
}

fn role_body_error_retry<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
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
        loop {
            {
                let i = probe.input();
                if role_body_boundary_pending(i) {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                }
                let character = i.input.remainder().chars().next()?;
                if matches!(character, '\r' | '\n') {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                }
                i.input.next()?;
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            if crate::grammar::expression::direct_canonical_statement_candidate(
                table,
                LeadingTrivia::None,
                probe,
            ) {
                let end = probe.input().pos();
                return Some((start..end, true));
            }
        }
    })?;
    emit_role_error(
        committed,
        crate::session::RoleDeclarationRole::Body,
        ExpectedSyntax::Statement,
        recovered.0,
    );
    Some(recovered.1)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CastTargetEpisodeSpec {
    stops: StopSet,
    scoped_frame: TypeExpressionScopedStopFrame,
    policy: TypeExpressionEpisodePolicy,
    outer_role: GrammarRole,
}

/// The target type sees Cast's form punctuation only for its own outer
/// TypeExpression episode. Recursive TypeExpression owners retain the raw
/// bits, while the scoped frame suspends the Cast authority beneath them.
fn cast_target_episode_spec(
    incoming: StopSet,
    current_episode_depth: usize,
    ambient_newline_owner: Option<DeclarationBracedNewlineOwner>,
) -> CastTargetEpisodeSpec {
    let mut stops = incoming.with(StopKind::Equal).with(StopKind::Semicolon);
    let mut scoped_stops = StopSet::default()
        .with(StopKind::Equal)
        .with(StopKind::Semicolon);
    if ambient_newline_owner.is_some() {
        stops = stops.with(StopKind::Newline);
        scoped_stops = scoped_stops.with(StopKind::Newline);
    }
    CastTargetEpisodeSpec {
        stops,
        scoped_frame: TypeExpressionScopedStopFrame {
            stops: scoped_stops,
            visible_episode_depth: current_episode_depth + 1,
        },
        policy: TypeExpressionEpisodePolicy::default(),
        outer_role: GrammarRole::Declaration(DeclarationRole::Cast(CastRole::TargetType)),
    }
}

fn parse_required_cast_target_type_isolated<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = cast_target_episode_spec(
        i.local.stop_set().unwrap_or_default(),
        i.local.type_expression_episode_depth(),
        declaration_braced_newline_owner_for_physical_newline(i.local),
    );
    i.local.push_stop_set(episode.stops);
    i.local
        .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    let parsed = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_outer_missing_role_and_policy(
                    Some(episode.outer_role),
                    episode.policy,
                    i,
                ),
            )
        }))
        .expect("the mandatory Cast target type entry is total");
    assert_eq!(
        i.local.pop_type_expression_scoped_stop_frame(),
        Some(episode.scoped_frame),
    );
    assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    match parsed {
        Recovered::Complete(parsed) => Recovered::Complete(Box::new(parsed)),
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

fn commit_required_cast_target_type_isolated<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = committed.probe(|probe| {
        let i = probe.input();
        cast_target_episode_spec(
            i.local.stop_set().unwrap_or_default(),
            i.local.type_expression_episode_depth(),
            declaration_braced_newline_owner_for_physical_newline(i.local),
        )
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(episode.stops);
        i.local
            .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    });
    let parsed = commit_direct_type_expression_with_outer_missing_role_and_policy(
        Some(episode.outer_role),
        episode.policy,
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(
            i.local.pop_type_expression_scoped_stop_frame(),
            Some(episode.scoped_frame),
        );
        assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    });
    let range = parsed.range();
    if range.is_empty() {
        Recovered::Incomplete
    } else {
        Recovered::Complete(range)
    }
}

fn cast_pattern_policy() -> PatternMandatorySlotPolicy {
    PatternMandatorySlotPolicy {
        fresh_primary_recovery_stops: StopSet::default()
            .with(StopKind::Colon)
            .with(StopKind::Equal),
        recovered_primary_tail_stops: StopSet::default().with(StopKind::Colon),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CastPrefixPhase {
    PatternIntroducer,
    PatternClose,
    TargetIntroducer,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CastPrefixTarget {
    OpenPattern,
    Pattern,
    LocalPatternClose,
    OuterPatternClose,
    TargetColon,
    TargetType,
    Form,
    Boundary,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CastPrefixInvalidRun {
    range: Range<usize>,
    target: CastPrefixTarget,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CastPatternHandoff {
    Target,
    Form,
    Boundary,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedCastPatternPhase<'source> {
    pattern: Recovered<CastPattern<'source>>,
    handoff: CastPatternHandoff,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CommittedCastPatternPhase {
    pattern: Recovered<Range<usize>>,
    handoff: CastPatternHandoff,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CommittedCastPatternValue {
    range: Range<usize>,
    complete: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CastTargetHandoff {
    Form,
    Boundary,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedCastTargetPhase<'source> {
    target: Recovered<CastTarget<'source>>,
    handoff: CastTargetHandoff,
}

/// The already-decided Cast prefix shared by Gate 3b's signature fixtures and
/// Gate 4b's form-aware AST adapter.  The boolean preserves whether the
/// prefix lattice established positive form-starter authority without making
/// the form judge re-probe Pattern or TypeExpression decisions.
struct ParsedCastSignature<'source> {
    visibility: Visibility,
    pattern: Recovered<CastPattern<'source>>,
    target: Recovered<CastTarget<'source>>,
    form_handoff: bool,
}

/// The direct-CST counterpart of [`ParsedCastSignature`].  Keeping the
/// already-decided form handoff out of the direct form judge means the latter
/// never re-probes a Pattern or TypeExpression boundary.
struct CommittedCastSignature {
    form_handoff: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CommittedCastTargetPhase {
    target: Recovered<Range<usize>>,
    handoff: CastTargetHandoff,
}

fn cast_target_type_candidate_input<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let errors_checkpoint = i.errors_checkpoint();
    let candidate = i.run(parse_type_expression).is_some();
    i.rollback(checkpoint);
    i.errors_rollback(errors_checkpoint);
    candidate
}

fn cast_prefix_outer_boundary_pending<E>(cast_base: usize, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty() || any_ambient_owner_claims(i) {
        return true;
    }
    if i.input.remainder().starts_with([',', ']', '}']) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let continues = mod_trivia(cast_base, i).is_some();
    i.rollback(checkpoint);
    !continues
}

fn cast_prefix_target<E>(
    phase: CastPrefixPhase,
    cast_base: usize,
    has_local_pattern_frame: bool,
    i: &mut SynIn<E>,
) -> Option<CastPrefixTarget>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if phase == CastPrefixPhase::PatternIntroducer {
        if i.input.remainder().starts_with('(') {
            return Some(CastPrefixTarget::OpenPattern);
        }
        // Composite Pattern NUDs such as `:symbol` outrank Cast's target
        // colon exactly as the neutral fresh-primary policy requires.
        if pattern_nud_candidate_input(i) {
            return Some(CastPrefixTarget::Pattern);
        }
    }
    if phase == CastPrefixPhase::TargetIntroducer && i.input.remainder().starts_with(':') {
        return Some(CastPrefixTarget::TargetColon);
    }
    if i.input.remainder().starts_with(')') {
        return Some(
            if has_local_pattern_frame && i.local.delimiter() == Some(Delimiter::Parenthesis) {
                CastPrefixTarget::LocalPatternClose
            } else {
                CastPrefixTarget::OuterPatternClose
            },
        );
    }
    if i.input.remainder().starts_with(':') {
        return Some(CastPrefixTarget::TargetColon);
    }
    if i.input.remainder().starts_with([';', '=']) {
        return Some(CastPrefixTarget::Form);
    }
    if phase == CastPrefixPhase::TargetIntroducer && cast_target_type_candidate_input(i) {
        return Some(CastPrefixTarget::TargetType);
    }
    cast_prefix_outer_boundary_pending(cast_base, i).then_some(CastPrefixTarget::Boundary)
}

/// Advances one prefix-slot invalid episode but leaves the first actual
/// retry candidate or downstream punctuation untouched. Trivia after the
/// first malformed byte belongs to the same Error range; a caller-owned
/// equal-or-shallower newline remains non-consuming.
fn scan_cast_prefix_invalid_run<E>(
    phase: CastPrefixPhase,
    cast_base: usize,
    has_local_pattern_frame: bool,
    i: &mut SynIn<E>,
) -> CastPrefixInvalidRun
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if let Some(target) = cast_prefix_target(phase, cast_base, has_local_pattern_frame, i) {
            return CastPrefixInvalidRun {
                range: start..i.pos(),
                target,
            };
        }
        let trivia_checkpoint = i.checkpoint();
        if let Some(trivia) = i.run(scan_trivia).filter(|trivia| !trivia.is_empty()) {
            debug_assert!(trivia.range().start >= start);
            continue;
        }
        i.rollback(trivia_checkpoint);
        i.input
            .next()
            .expect("a non-boundary Cast invalid byte remains available");
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn cast_pattern_handoff(target: CastPrefixTarget) -> CastPatternHandoff {
    match target {
        CastPrefixTarget::LocalPatternClose | CastPrefixTarget::TargetColon => {
            CastPatternHandoff::Target
        }
        CastPrefixTarget::Form => CastPatternHandoff::Form,
        CastPrefixTarget::OuterPatternClose | CastPrefixTarget::Boundary => {
            CastPatternHandoff::Boundary
        }
        CastPrefixTarget::OpenPattern
        | CastPrefixTarget::Pattern
        | CastPrefixTarget::TargetType => {
            unreachable!("a completed Cast pattern phase cannot hand off to this target")
        }
    }
}

fn emit_cast_recovery<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: GrammarRole,
    expected: ExpectedSyntax,
    kind: RecoveryKind,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let unexpected = match kind {
            RecoveryKind::Missing => Arc::from([]),
            RecoveryKind::Error => Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
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

fn emit_cast_slot_recovery<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: CastRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let kind = if range.is_empty() {
        RecoveryKind::Missing
    } else {
        RecoveryKind::Error
    };
    emit_cast_recovery(
        committed,
        GrammarRole::Declaration(DeclarationRole::Cast(role)),
        expected,
        kind,
        range,
    );
}

/// `;` and an exact declaration `=` are both positive, Cast-owned evidence
/// for the form slot.  Keep the two alternatives in its one recovery record
/// instead of making a malformed run manufacture two independent misses.
fn emit_cast_body_introducer_recovery<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let kind = if range.is_empty() {
        RecoveryKind::Missing
    } else {
        RecoveryKind::Error
    };
    let role = GrammarRole::Declaration(DeclarationRole::Cast(CastRole::BodyIntroducer));
    let record = committed.probe(|probe| {
        let i = probe.input();
        let unexpected = match kind {
            RecoveryKind::Missing => Arc::from([]),
            RecoveryKind::Error => Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
        };
        let source = ExpectationSources::COMMITTED_RECOVERY_RULE;
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            kind,
            unexpected,
            Arc::from([
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Semicolon,
                    ),
                    range: range.clone(),
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Equals,
                    ),
                    range: range.clone(),
                    sources: source,
                },
            ]),
            0,
        )
    });
    match kind {
        RecoveryKind::Missing => committed.emit_missing(record),
        RecoveryKind::Error => committed.emit_error(record),
    }
}

fn emit_cast_pattern_close_recovery<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let kind = if range.is_empty() {
        RecoveryKind::Missing
    } else {
        RecoveryKind::Error
    };
    emit_cast_recovery(
        committed,
        GrammarRole::ClosingDelimiter {
            owner: ConstructRole::CastPattern,
            delimiter: Delimiter::Parenthesis,
        },
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
            Delimiter::Parenthesis,
        )),
        kind,
        range,
    );
}

fn parse_required_cast_pattern_value_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<Pattern<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.run(from_fn(|i| {
        Some(parse_required_pattern_with_outer_missing_role_and_policy(
            table,
            Some(GrammarRole::Declaration(DeclarationRole::Cast(
                CastRole::Pattern,
            ))),
            cast_pattern_policy(),
            i,
        ))
    }))
    .expect("the mandatory Cast pattern entry is total")
}

fn commit_required_cast_pattern_value_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> CommittedCastPatternValue
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let parsed = commit_direct_pattern_with_outer_missing_role_and_policy(
        table,
        LeadingTrivia::None,
        Some(GrammarRole::Declaration(DeclarationRole::Cast(
            CastRole::Pattern,
        ))),
        cast_pattern_policy(),
        committed,
    );
    CommittedCastPatternValue {
        range: parsed.range(),
        complete: parsed.is_complete(),
    }
}

fn parse_cast_pattern_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    cast_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ParsedCastPatternPhase<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading_checkpoint = i.checkpoint();
    if mod_trivia(cast_base, i).is_none() {
        i.rollback(leading_checkpoint);
        return ParsedCastPatternPhase {
            pattern: Recovered::Incomplete,
            handoff: CastPatternHandoff::Boundary,
        };
    }
    let introducer =
        scan_cast_prefix_invalid_run(CastPrefixPhase::PatternIntroducer, cast_base, false, i);
    let has_group_evidence = matches!(
        introducer.target,
        CastPrefixTarget::OpenPattern | CastPrefixTarget::Pattern
    );
    if !has_group_evidence {
        return ParsedCastPatternPhase {
            pattern: Recovered::Incomplete,
            handoff: cast_pattern_handoff(introducer.target),
        };
    }
    let open = if introducer.target == CastPrefixTarget::OpenPattern {
        i.run(from_fn(|mut i| scan_character(&mut i, '(')))
    } else {
        None
    };
    let has_local_frame = open.is_some();
    if has_local_frame {
        let _ = mod_trivia(cast_base, i);
    }
    let value_start = i.pos();
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
        .with(StopKind::RightParenthesis);
    i.local.push_stop_set(stops);
    if has_local_frame {
        i.local.push_delimiter(Delimiter::Parenthesis);
    }
    let value = parse_required_cast_pattern_value_isolated(table, i);
    let value_complete = matches!(value, Recovered::Complete(_));
    let close_trivia_checkpoint = i.checkpoint();
    if mod_trivia(cast_base, i).is_none() {
        i.rollback(close_trivia_checkpoint);
    }
    let (close, handoff) = if !value_complete {
        let target =
            cast_prefix_target(CastPrefixPhase::PatternClose, cast_base, has_local_frame, i)
                .unwrap_or(CastPrefixTarget::Boundary);
        if target == CastPrefixTarget::LocalPatternClose {
            let close = i
                .run(from_fn(|mut i| scan_character(&mut i, ')')))
                .expect("the inspected Cast-local close remains available");
            (Recovered::Complete(close), CastPatternHandoff::Target)
        } else {
            (Recovered::Incomplete, cast_pattern_handoff(target))
        }
    } else {
        let recovery = scan_cast_prefix_invalid_run(
            CastPrefixPhase::PatternClose,
            cast_base,
            has_local_frame,
            i,
        );
        if recovery.target == CastPrefixTarget::LocalPatternClose {
            let close = i
                .run(from_fn(|mut i| scan_character(&mut i, ')')))
                .expect("the inspected Cast-local close remains available");
            (Recovered::Complete(close), CastPatternHandoff::Target)
        } else {
            (Recovered::Incomplete, cast_pattern_handoff(recovery.target))
        }
    };
    if has_local_frame {
        assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    }
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    let start = open.as_ref().map_or(value_start, |range| range.start);
    let end = i.pos().max(start);
    ParsedCastPatternPhase {
        pattern: Recovered::Complete(CastPattern {
            open: open.map_or(Recovered::Incomplete, Recovered::Complete),
            value,
            close,
            range: start..end,
        }),
        handoff,
    }
}

fn commit_cast_pattern_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    cast_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> CommittedCastPatternPhase
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = committed.probe(|probe| mod_trivia(cast_base, probe.input()));
    let Some(leading) = leading else {
        let at = committed.probe(|probe| probe.input().pos());
        emit_cast_slot_recovery(
            committed,
            CastRole::PatternIntroducer,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(
                Delimiter::Parenthesis,
            )),
            at..at,
        );
        return CommittedCastPatternPhase {
            pattern: Recovered::Incomplete,
            handoff: CastPatternHandoff::Boundary,
        };
    };
    committed.emit_trivia(&leading);
    let introducer = committed.probe(|probe| {
        scan_cast_prefix_invalid_run(
            CastPrefixPhase::PatternIntroducer,
            cast_base,
            false,
            probe.input(),
        )
    });
    let has_group_evidence = matches!(
        introducer.target,
        CastPrefixTarget::OpenPattern | CastPrefixTarget::Pattern
    );
    if !has_group_evidence {
        emit_cast_slot_recovery(
            committed,
            CastRole::PatternIntroducer,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(
                Delimiter::Parenthesis,
            )),
            introducer.range,
        );
        return CommittedCastPatternPhase {
            pattern: Recovered::Incomplete,
            handoff: cast_pattern_handoff(introducer.target),
        };
    }
    committed.start_node(SyntaxKind::CastPattern);
    if introducer.target == CastPrefixTarget::Pattern || !introducer.range.is_empty() {
        emit_cast_slot_recovery(
            committed,
            CastRole::PatternIntroducer,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(
                Delimiter::Parenthesis,
            )),
            introducer.range.clone(),
        );
    }
    let open = if introducer.target == CastPrefixTarget::OpenPattern {
        commit_character(committed, '(')
    } else {
        None
    };
    if let Some(open) = &open {
        committed.token(SyntaxKind::LParen, open.clone());
    }
    let has_local_frame = open.is_some();
    if has_local_frame {
        if let Some(trivia) = committed.probe(|probe| mod_trivia(cast_base, probe.input())) {
            committed.emit_trivia(&trivia);
        }
    }
    let value_start = committed.probe(|probe| probe.input().pos());
    let stops = committed.probe(|probe| {
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
            .with(StopKind::RightParenthesis)
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(stops);
        if has_local_frame {
            i.local.push_delimiter(Delimiter::Parenthesis);
        }
    });
    let value = commit_required_cast_pattern_value_isolated(table, committed);
    if let Some(trivia) = committed.probe(|probe| mod_trivia(cast_base, probe.input())) {
        committed.emit_trivia(&trivia);
    }
    let (close, handoff) = if !value.complete {
        let target = committed.probe(|probe| {
            cast_prefix_target(
                CastPrefixPhase::PatternClose,
                cast_base,
                has_local_frame,
                probe.input(),
            )
            .unwrap_or(CastPrefixTarget::Boundary)
        });
        if target == CastPrefixTarget::LocalPatternClose {
            let close = commit_character(committed, ')')
                .expect("the inspected Cast-local close remains available");
            committed.token(SyntaxKind::RParen, close.clone());
            (Some(close), CastPatternHandoff::Target)
        } else {
            (None, cast_pattern_handoff(target))
        }
    } else {
        let recovery = committed.probe(|probe| {
            scan_cast_prefix_invalid_run(
                CastPrefixPhase::PatternClose,
                cast_base,
                has_local_frame,
                probe.input(),
            )
        });
        if recovery.range.is_empty() && recovery.target == CastPrefixTarget::LocalPatternClose {
            let close = commit_character(committed, ')')
                .expect("the inspected Cast-local close remains available");
            committed.token(SyntaxKind::RParen, close.clone());
            (Some(close), CastPatternHandoff::Target)
        } else {
            emit_cast_pattern_close_recovery(committed, recovery.range);
            if recovery.target == CastPrefixTarget::LocalPatternClose {
                let close = commit_character(committed, ')')
                    .expect("the inspected Cast-local close remains available");
                committed.token(SyntaxKind::RParen, close.clone());
                (Some(close), CastPatternHandoff::Target)
            } else {
                (None, cast_pattern_handoff(recovery.target))
            }
        }
    };
    committed.probe(|probe| {
        let i = probe.input();
        if has_local_frame {
            assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
        }
        assert_eq!(i.local.pop_stop_set(), Some(stops));
    });
    let start = open.as_ref().map_or(value_start, |range| range.start);
    let end = committed.probe(|probe| probe.input().pos()).max(start);
    committed.finish_node();
    let _ = close;
    CommittedCastPatternPhase {
        pattern: Recovered::Complete(start..end),
        handoff,
    }
}

fn parse_cast_target_isolated<'source, E>(
    cast_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ParsedCastTargetPhase<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    if mod_trivia(cast_base, i).is_none() {
        i.rollback(checkpoint);
        return ParsedCastTargetPhase {
            target: Recovered::Incomplete,
            handoff: CastTargetHandoff::Boundary,
        };
    }
    let introducer =
        scan_cast_prefix_invalid_run(CastPrefixPhase::TargetIntroducer, cast_base, false, i);
    let has_target_evidence = matches!(
        introducer.target,
        CastPrefixTarget::TargetColon | CastPrefixTarget::TargetType
    );
    if !has_target_evidence {
        return ParsedCastTargetPhase {
            target: Recovered::Incomplete,
            handoff: if introducer.target == CastPrefixTarget::Form {
                CastTargetHandoff::Form
            } else {
                CastTargetHandoff::Boundary
            },
        };
    }
    let colon = if introducer.target == CastPrefixTarget::TargetColon {
        i.run(from_fn(|mut i| scan_character(&mut i, ':')))
    } else {
        None
    };
    if colon.is_some() {
        let _ = mod_trivia(cast_base, i);
    }
    let value_start = i.pos();
    let value = parse_required_cast_target_type_isolated(i);
    let complete = matches!(value, Recovered::Complete(_));
    let start = colon.as_ref().map_or(value_start, |range| range.start);
    let end = i.pos().max(start);
    ParsedCastTargetPhase {
        target: Recovered::Complete(CastTarget {
            colon: colon.map_or(Recovered::Incomplete, Recovered::Complete),
            value,
            range: start..end,
        }),
        handoff: if complete || i.input.remainder().starts_with([';', '=']) {
            CastTargetHandoff::Form
        } else {
            CastTargetHandoff::Boundary
        },
    }
}

fn commit_cast_target_isolated<'parse, 'source, 'local, E, O>(
    cast_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> CommittedCastTargetPhase
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = committed.probe(|probe| mod_trivia(cast_base, probe.input()));
    let Some(leading) = leading else {
        let at = committed.probe(|probe| probe.input().pos());
        emit_cast_slot_recovery(
            committed,
            CastRole::TargetIntroducer,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
            at..at,
        );
        return CommittedCastTargetPhase {
            target: Recovered::Incomplete,
            handoff: CastTargetHandoff::Boundary,
        };
    };
    committed.emit_trivia(&leading);
    let introducer = committed.probe(|probe| {
        scan_cast_prefix_invalid_run(
            CastPrefixPhase::TargetIntroducer,
            cast_base,
            false,
            probe.input(),
        )
    });
    let has_target_evidence = matches!(
        introducer.target,
        CastPrefixTarget::TargetColon | CastPrefixTarget::TargetType
    );
    if !has_target_evidence {
        emit_cast_slot_recovery(
            committed,
            CastRole::TargetIntroducer,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
            introducer.range,
        );
        return CommittedCastTargetPhase {
            target: Recovered::Incomplete,
            handoff: if introducer.target == CastPrefixTarget::Form {
                CastTargetHandoff::Form
            } else {
                CastTargetHandoff::Boundary
            },
        };
    }
    committed.start_node(SyntaxKind::CastTarget);
    if introducer.target == CastPrefixTarget::TargetType || !introducer.range.is_empty() {
        emit_cast_slot_recovery(
            committed,
            CastRole::TargetIntroducer,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
            introducer.range.clone(),
        );
    }
    let colon = if introducer.target == CastPrefixTarget::TargetColon {
        commit_character(committed, ':')
    } else {
        None
    };
    if let Some(colon) = &colon {
        committed.token(SyntaxKind::Colon, colon.clone());
    }
    if colon.is_some() {
        if let Some(trivia) = committed.probe(|probe| mod_trivia(cast_base, probe.input())) {
            committed.emit_trivia(&trivia);
        }
    }
    let value_start = committed.probe(|probe| probe.input().pos());
    let value = commit_required_cast_target_type_isolated(committed);
    let complete = matches!(value, Recovered::Complete(_));
    let start = colon.as_ref().map_or(value_start, |range| range.start);
    let end = committed.probe(|probe| probe.input().pos()).max(start);
    committed.finish_node();
    CommittedCastTargetPhase {
        target: Recovered::Complete(start..end),
        handoff: if complete
            || committed.probe(|probe| probe.input().input.remainder().starts_with([';', '=']))
        {
            CastTargetHandoff::Form
        } else {
            CastTargetHandoff::Boundary
        },
    }
}

fn parse_cast_signature_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<CastDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let intro = i.run(recognize_cast_statement_intro)?;
    let signature = parse_cast_signature_after_intro_isolated(table, &intro, &mut i);
    let declaration = CastDeclaration {
        visibility: signature.visibility,
        pattern: signature.pattern,
        target: signature.target,
        form: Recovered::Incomplete,
        range: intro.start..i.pos(),
    };
    i.errors_rollback(errors_checkpoint);
    Some(declaration)
}

/// Gate 3b's Pattern/Target prefix composition, kept separate from the
/// declaration form so later consumers never duplicate its handoff logic.
fn parse_cast_signature_after_intro_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    intro: &CastStatementIntro<'source>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ParsedCastSignature<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let visibility = intro
        .visibility
        .as_ref()
        .map_or(Visibility::Private, |prefix| prefix.visibility);
    let pattern = parse_cast_pattern_isolated(table, intro.cast_base, i);
    let (target, form_handoff) = match pattern.handoff {
        CastPatternHandoff::Target => {
            let target = parse_cast_target_isolated(intro.cast_base, i);
            (target.target, target.handoff == CastTargetHandoff::Form)
        }
        CastPatternHandoff::Form => (Recovered::Incomplete, true),
        CastPatternHandoff::Boundary => (Recovered::Incomplete, false),
    };
    ParsedCastSignature {
        visibility,
        pattern: pattern.pattern,
        target,
        form_handoff,
    }
}

/// Gate 4b's isolated, form-aware Cast AST adapter.  It deliberately builds
/// no CST and remains unreachable from real statement dispatch until Gate 8.
pub(crate) fn parse_cast_declaration_form_aware_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<CastDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let intro = i.run(recognize_cast_statement_intro)?;
    let signature = parse_cast_signature_after_intro_isolated(table, &intro, &mut i);
    let form = signature
        .form_handoff
        .then(|| parse_cast_form_isolated(table, intro.cast_base, &mut i))
        .unwrap_or(Recovered::Incomplete);
    let declaration = CastDeclaration {
        visibility: signature.visibility,
        pattern: signature.pattern,
        target: signature.target,
        form,
        range: intro.start..i.pos(),
    };
    i.errors_rollback(errors_checkpoint);
    Some(declaration)
}

/// Selects the only two standalone Cast forms.  The post-equals body uses the
/// neutral Binding-style layout decision but supplies Cast-owned AST builders.
fn parse_cast_form_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    cast_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<CastForm<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return Recovered::Incomplete;
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(cast_base, i) else {
        i.rollback(checkpoint);
        return Recovered::Incomplete;
    };
    if let Some(semicolon) = i.run(scan_punctuation).and_then(|punctuation| {
        (punctuation.kind() == PunctuationKind::Semicolon).then_some(punctuation.range())
    }) {
        return Recovered::Complete(CastForm::Bodyless { semicolon });
    }

    i.rollback(checkpoint.clone());
    let Some(_) = mod_trivia(cast_base, i) else {
        i.rollback(checkpoint);
        return Recovered::Incomplete;
    };
    let Some(equals) = i.run(scan_declaration_exact_equals) else {
        i.rollback(checkpoint);
        return cast_body_introducer_error_retry_ast(i)
            .filter(|retry| *retry)
            .map_or(Recovered::Incomplete, |_| {
                parse_cast_form_isolated(table, cast_base, i)
            });
    };
    let body = parse_binding_style_body(
        cast_base,
        |_trivia, i| {
            i.run(from_fn(|i| parse_expression_with_operators(table, i)))
                .or_else(|| {
                    cast_inline_body_error_retry_ast(table, i)
                        .is_some_and(|retry| retry)
                        .then(|| i.run(from_fn(|i| parse_expression_with_operators(table, i))))
                        .flatten()
                })
                .map(|expression| CastBody::Inline { expression })
        },
        |trivia, block_indent, i| CastBody::Indented {
            block: parse_indented_cast_body(table, trivia, cast_base, block_indent, i),
        },
        i,
    )
    .map_or(Recovered::Incomplete, Recovered::Complete);
    let end = match &body {
        Recovered::Complete(CastBody::Inline { expression }) => expression.range().end,
        Recovered::Complete(CastBody::Indented { block }) => block.range().end,
        Recovered::Incomplete => equals.end,
    };
    Recovered::Complete(CastForm::Definition {
        equals: equals.clone(),
        body,
        range: equals.start..end,
    })
}

fn commit_cast_signature_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    intro: CastStatementIntro<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    committed.start_node(SyntaxKind::CastDeclaration);
    let _ = commit_cast_signature_after_intro_isolated(table, &intro, committed);
    let end = committed.probe(|probe| probe.input().pos());
    committed.finish_node();
    committed.probe(|probe| {
        probe.input().errors_rollback(errors_checkpoint);
    });
    Recovered::Complete(intro.start..end)
}

/// Emits Gate 3b's already-decided Cast prefix without choosing its form.
/// Both the prefix-only fixture harness and Gate 5's full declaration adapter
/// call this one continuation so their Pattern/Target ownership stays exact.
fn commit_cast_signature_after_intro_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    intro: &CastStatementIntro<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> CommittedCastSignature
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::CastKw, intro.cast_keyword.range());
    let pattern = commit_cast_pattern_isolated(table, intro.cast_base, committed);
    let form_handoff = match pattern.handoff {
        CastPatternHandoff::Target => {
            commit_cast_target_isolated(intro.cast_base, committed).handoff
                == CastTargetHandoff::Form
        }
        CastPatternHandoff::Form => true,
        CastPatternHandoff::Boundary => false,
    };
    CommittedCastSignature { form_handoff }
}

/// Gate 5's direct-CST form judge.  It shares the Binding-style body layout
/// decision but owns CastBody emission and Cast-specific recovery identity.
fn commit_cast_form_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    cast_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        return Recovered::Incomplete;
    }

    let bodyless = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let semicolon = mod_trivia(cast_base, i)
            .and_then(|_| i.run(scan_punctuation))
            .filter(|punctuation| punctuation.kind() == PunctuationKind::Semicolon)
            .map(|punctuation| punctuation.range());
        i.rollback(checkpoint);
        semicolon
    });
    if bodyless.is_some() {
        let trivia = committed
            .probe(|probe| mod_trivia(cast_base, probe.input()))
            .expect("the committed bodyless Cast trivia was already classified");
        committed.emit_trivia(&trivia);
        let semicolon = commit_character(committed, ';')
            .expect("the committed bodyless Cast semicolon was already classified");
        committed.token(SyntaxKind::Semicolon, semicolon.clone());
        return Recovered::Complete(semicolon.clone());
    }

    let equals = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let equals = mod_trivia(cast_base, i).and_then(|_| i.run(scan_declaration_exact_equals));
        i.rollback(checkpoint);
        equals
    });
    if equals.is_none() {
        let trivia = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let trivia = mod_trivia(cast_base, i);
            i.rollback(checkpoint);
            trivia
        });
        let Some(trivia) = trivia else {
            let at = committed.probe(|probe| probe.input().pos());
            emit_cast_body_introducer_recovery(committed, at..at);
            return Recovered::Incomplete;
        };
        let newline = committed
            .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
        if newline {
            let at = committed.probe(|probe| probe.input().pos());
            emit_cast_body_introducer_recovery(committed, at..at);
            return Recovered::Incomplete;
        }
        let consumed_trivia = committed
            .probe(|probe| mod_trivia(cast_base, probe.input()))
            .expect("the Cast form recovery leaves its trivia at the cursor");
        assert_eq!(consumed_trivia.range(), trivia.range());
        committed.emit_trivia(&consumed_trivia);
        return match cast_body_introducer_error_retry(committed) {
            Some(true) => commit_cast_form_isolated(table, cast_base, committed),
            Some(false) => Recovered::Incomplete,
            None => {
                let at = committed.probe(|probe| probe.input().pos());
                emit_cast_body_introducer_recovery(committed, at..at);
                Recovered::Incomplete
            }
        };
    }
    let trivia = committed
        .probe(|probe| mod_trivia(cast_base, probe.input()))
        .expect("the committed Cast definition trivia was already classified");
    committed.emit_trivia(&trivia);
    let equals = committed
        .probe(|probe| probe.input().run(scan_declaration_exact_equals))
        .expect("the committed Cast definition equals was already classified");
    committed.token(SyntaxKind::Equals, equals.clone());

    let body_start = committed.probe(|probe| probe.input().pos());
    committed.start_node(SyntaxKind::CastBody);
    let body = commit_binding_style_body(
        table,
        cast_base,
        GrammarRole::Declaration(DeclarationRole::Cast(CastRole::Body)),
        |expression| expression.range(),
        |opening_trivia, block_indent, committed| {
            commit_indented_cast_body(table, opening_trivia, cast_base, block_indent, committed);
            body_start..committed.probe(|probe| probe.input().pos())
        },
        |committed| cast_inline_body_error_retry(table, committed),
        committed,
    );
    committed.finish_node();
    let end = match body {
        Recovered::Complete(range) => range.end,
        Recovered::Incomplete => equals.end,
    };
    Recovered::Complete(equals.start..end)
}

fn cast_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i
        .run(scan_punctuation)
        .is_some_and(|punctuation| punctuation.kind() == PunctuationKind::Semicolon)
        || i.run(scan_declaration_exact_equals).is_some();
    i.rollback(checkpoint);
    pending
}

/// A Cast form has no authority over a following declaration, caller close,
/// or target colon.  Those are safe points for the one BodyIntroducer error
/// episode and remain unconsumed for their real owner.
fn cast_body_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Comma
                | PunctuationKind::Close(
                    Delimiter::Parenthesis | Delimiter::Bracket | Delimiter::Brace
                )
                | PunctuationKind::Colon
        )
    });
    i.rollback(checkpoint);
    pending
}

/// AST half of the BodyIntroducer recovery lattice.  Direct CST realizes the
/// matching typed Error below; both leave the discovered starter/boundary in
/// place for the same-slot retry or its outer owner.
fn cast_body_introducer_error_retry_ast<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if cast_body_starter_pending(i) {
            return (start < i.pos()).then_some(true);
        }
        if cast_body_boundary_pending(i) {
            return (start < i.pos()).then_some(false);
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < i.pos()).then_some(false);
        };
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(false);
        }
        let operator_run = declaration_operator_character(character);
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        if operator_run {
            while i
                .input
                .remainder()
                .chars()
                .next()
                .is_some_and(declaration_operator_character)
            {
                i.input.next()?;
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            continue;
        }
    }
}

fn cast_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
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
        loop {
            let i = probe.input();
            if cast_body_starter_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), true));
            }
            if cast_body_boundary_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            let Some(character) = i.input.remainder().chars().next() else {
                return (start < i.pos()).then_some((start..i.pos(), false));
            };
            if matches!(character, '\r' | '\n') {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            let operator_run = declaration_operator_character(character);
            i.input.next()?;
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            if operator_run {
                while i
                    .input
                    .remainder()
                    .chars()
                    .next()
                    .is_some_and(declaration_operator_character)
                {
                    i.input.next()?;
                    let mut line = i.local.line();
                    line.at_line_start = false;
                    i.local.set_line(line);
                }
                continue;
            }
        }
    })?;
    emit_cast_body_introducer_recovery(committed, recovered.0);
    Some(recovered.1)
}

fn cast_inline_body_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Semicolon
                | PunctuationKind::Comma
                | PunctuationKind::Close(
                    Delimiter::Parenthesis | Delimiter::Bracket | Delimiter::Brace
                )
        )
    });
    i.rollback(checkpoint);
    pending
}

fn cast_inline_body_error_retry_ast<'source, E>(
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
        if cast_inline_body_boundary_pending(i) {
            return (start < i.pos()).then_some(false);
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < i.pos()).then_some(false);
        };
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        let checkpoint = i.checkpoint();
        let candidate = i
            .run(from_fn(|i| parse_expression_with_operators(table, i)))
            .is_some();
        i.rollback(checkpoint);
        if candidate {
            return Some(true);
        }
    }
}

fn cast_inline_body_error_retry<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> BindingStyleInlineRecovery
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        loop {
            {
                let i = probe.input();
                if cast_inline_body_boundary_pending(i) {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                }
                let Some(character) = i.input.remainder().chars().next() else {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                };
                if matches!(character, '\r' | '\n') {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                }
                i.input.next()?;
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            if crate::grammar::expression::direct_expression_nud_candidate(
                table,
                LeadingTrivia::None,
                probe,
            ) {
                let end = probe.input().pos();
                return Some((start..end, true));
            }
        }
    });
    let Some((range, retry)) = recovered else {
        return BindingStyleInlineRecovery::None;
    };
    emit_cast_slot_recovery(committed, CastRole::Body, ExpectedSyntax::Expression, range);
    if retry {
        BindingStyleInlineRecovery::Retry
    } else {
        BindingStyleInlineRecovery::TerminalError
    }
}

/// Gate 5's full direct-CST isolated adapter.  It stays deliberately outside
/// real statement dispatch until the Gate 8 atomic promotion.
pub(crate) fn commit_cast_declaration_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    intro: CastStatementIntro<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    committed.start_node(SyntaxKind::CastDeclaration);
    let signature = commit_cast_signature_after_intro_isolated(table, &intro, committed);
    if signature.form_handoff {
        let _ = commit_cast_form_isolated(table, intro.cast_base, committed);
    }
    let end = committed.probe(|probe| probe.input().pos());
    committed.finish_node();
    committed.probe(|probe| {
        probe.input().errors_rollback(errors_checkpoint);
    });
    Recovered::Complete(intro.start..end)
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedImplTail<'source> {
    head: Recovered<Box<TypeExpression<'source>>>,
    description: Option<ImplDescription<'source>>,
    body: Recovered<ImplBody<'source>>,
}

/// Standalone AST adapter used by root and canonical Statement dispatch.
/// Intro recognition and declaration realization stay here; the post-keyword
/// grammar is shared with the future Type-owned adapter.
pub(crate) fn parse_impl_declaration_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ImplDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let declaration = (|| {
        let intro = i.run(recognize_impl_statement_intro)?;
        let visibility = intro
            .visibility
            .map_or(Visibility::Private, |prefix| prefix.visibility);
        let tail = parse_impl_tail_ast(
            table,
            standalone_impl_tail_owner_spec(intro.impl_base),
            &mut i,
        );
        let end = i.pos();
        Some(ImplDeclaration {
            visibility,
            head: tail.head,
            description: tail.description,
            body: tail.body,
            range: intro.start..end,
        })
    })();
    i.errors_rollback(errors_checkpoint);
    declaration
}

fn parse_impl_tail_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ParsedImplTail<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let head = if any_ambient_owner_claims(i) {
        Recovered::Incomplete
    } else {
        let checkpoint = i.checkpoint();
        if mod_trivia(owner_spec.owner_base, i).is_some() {
            parse_required_impl_tail_type_expression(owner_spec, ImplTypeExpressionSlot::Head, i)
        } else {
            i.rollback(checkpoint);
            Recovered::Incomplete
        }
    };
    let (description, body) = parse_impl_after_head_ast(table, owner_spec, i);
    ParsedImplTail {
        head,
        description,
        body,
    }
}

/// Type-owned AST realization after the sink-free post-header judge has cut
/// to its exact `impl` evidence. The shared tail supplies every post-keyword
/// slot; this adapter contributes only the Type form payload and its range.
fn parse_type_attached_impl_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    start: TypeAttachedImplStart<'source>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> TypeAttachedImpl<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let leading = i
        .run(scan_trivia)
        .expect("the accepted Type-attached Impl gap remains at the cursor");
    debug_assert_eq!(leading.range(), start.leading.range());
    let keyword = i
        .run(scan_word)
        .expect("the accepted Type-attached Impl keyword remains at the cursor");
    debug_assert_eq!(keyword.range(), start.keyword.range());
    debug_assert_eq!(keyword.text(), "impl");

    let tail = parse_impl_tail_ast(
        table,
        type_attached_impl_tail_owner_spec(start.type_base),
        i,
    );
    let end = i.pos();
    let attached = TypeAttachedImpl {
        impl_keyword: keyword.range(),
        head: tail.head,
        description: tail.description,
        body: tail.body,
        range: keyword.range().start..end,
    };
    i.errors_rollback(errors_checkpoint);
    attached
}

fn parse_impl_after_head_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (
    Option<ImplDescription<'source>>,
    Recovered<ImplBody<'source>>,
)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return (None, Recovered::Incomplete);
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(owner_spec.owner_base, i) else {
        i.rollback(checkpoint);
        return (None, Recovered::Incomplete);
    };
    let colon = i.run(scan_punctuation).and_then(|punctuation| {
        (punctuation.kind() == PunctuationKind::Colon).then_some(punctuation.range())
    });
    let Some(colon) = colon else {
        i.rollback(checkpoint);
        return (None, parse_impl_body_ast(table, owner_spec, i));
    };

    let description_trivia_checkpoint = i.checkpoint();
    let description_trivia = i.run(scan_trivia).expect("trivia scan is total");
    if i.input.source()[description_trivia.range()].contains(['\r', '\n']) {
        i.rollback(description_trivia_checkpoint);
        i.rollback(checkpoint);
        return (None, parse_impl_body_ast(table, owner_spec, i));
    }
    let value = parse_required_impl_tail_type_expression(
        owner_spec,
        ImplTypeExpressionSlot::Description,
        i,
    );
    let description = ImplDescription {
        colon: colon.clone(),
        value,
        range: colon.start..i.pos(),
    };
    let body = parse_impl_body_ast(table, owner_spec, i);
    (Some(description), body)
}

fn parse_impl_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<ImplBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return Recovered::Incomplete;
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(owner_spec.owner_base, i) else {
        i.rollback(checkpoint);
        return Recovered::Incomplete;
    };
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        if impl_body_introducer_error_retry_ast(i).is_some_and(|retry| retry) {
            return parse_impl_body_ast(table, owner_spec, i);
        }
        return Recovered::Incomplete;
    };
    match punctuation.kind() {
        PunctuationKind::Semicolon => Recovered::Complete(ImplBody::Bodyless {
            semicolon: punctuation.range(),
        }),
        PunctuationKind::Open(Delimiter::Brace) => Recovered::Complete(ImplBody::Braced {
            block: parse_braced_statement_block_expression(table, punctuation.range(), i),
        }),
        PunctuationKind::Colon => Recovered::Complete(ImplBody::Colon {
            colon: punctuation.range(),
            body: parse_impl_colon_body_ast(table, owner_spec, i)
                .map_or(Recovered::Incomplete, Recovered::Complete),
        }),
        _ => {
            i.rollback(checkpoint);
            if impl_body_introducer_error_retry_ast(i).is_some_and(|retry| retry) {
                return parse_impl_body_ast(table, owner_spec, i);
            }
            Recovered::Incomplete
        }
    }
}

fn parse_impl_colon_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<ImplColonBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia)?;
    if i.input.source()[trivia.range()].contains(['\r', '\n']) {
        if i.local.line().line_indent <= owner_spec.owner_base {
            i.rollback(checkpoint);
            return None;
        }
        let block_indent = i.local.line().line_indent;
        return Some(ImplColonBody::Indented {
            block: parse_indented_impl_tail_body(
                table,
                trivia,
                owner_spec.owner_base,
                block_indent,
                owner_spec.grammar_role(ImplRole::IndentedStatement),
                i,
            ),
        });
    }
    let ambient_scope = i.local.push_inline_canonical_statement_ambient_scope(
        crate::session::InlineStatementOwnerKind::ImplColonBody,
    );
    let statement = i
        .run(from_fn(|i| parse_canonical_statement(table, i)))
        .or_else(|| {
            impl_body_error_retry_ast(table, i)
                .is_some_and(|retry| retry)
                .then(|| i.run(from_fn(|i| parse_canonical_statement(table, i))))
                .flatten()
        });
    let body = statement.map(|statement| {
        let terminal = i.checkpoint();
        if i.run(scan_punctuation)
            .is_none_or(|punctuation| punctuation.kind() != PunctuationKind::Semicolon)
        {
            i.rollback(terminal);
        }
        ImplColonBody::Inline {
            statement: Box::new(statement),
        }
    });
    assert_eq!(i.local.pop_ambient_owner_scope(), Some(ambient_scope));
    body
}

/// Standalone direct-CST adapter. The caller-owned wrapper ends at `ImplKw`;
/// [`commit_impl_tail`] emits only the shared post-keyword continuation.
pub(crate) fn commit_impl_declaration_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: ImplStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    committed.start_node(SyntaxKind::ImplDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::ImplKw, intro.impl_keyword.range());
    commit_impl_tail(
        table,
        standalone_impl_tail_owner_spec(intro.impl_base),
        committed,
    );
    let end = committed_position(committed);
    committed.finish_node();
    committed.probe(|probe| {
        probe.input().errors_rollback(errors_checkpoint);
    });
    Recovered::Complete(intro.start..end)
}

fn commit_impl_tail<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let head_terminated_incomplete =
        if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
            emit_impl_tail_missing(
                owner_spec,
                committed,
                ImplRole::Head,
                ExpectedSyntax::TypeExpression,
            );
            true
        } else if let Some(trivia) =
            committed.probe(|probe| mod_trivia(owner_spec.owner_base, probe.input()))
        {
            committed.emit_trivia(&trivia);
            matches!(
                commit_required_impl_tail_type_expression(
                    owner_spec,
                    ImplTypeExpressionSlot::Head,
                    committed,
                ),
                Recovered::Incomplete
            )
        } else {
            emit_impl_tail_missing(
                owner_spec,
                committed,
                ImplRole::Head,
                ExpectedSyntax::TypeExpression,
            );
            true
        };

    commit_impl_after_head(table, owner_spec, committed, head_terminated_incomplete);
}

/// Type-owned direct-CST realization for a caller that already opened its
/// `TypeDeclaration` and emitted the shared header. No declaration wrapper is
/// started here: the accepted gap, `ImplKw`, and shared tail remain flat
/// children of that caller-owned node.
fn commit_type_attached_impl_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    start: TypeAttachedImplStart<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    let leading = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("the accepted Type-attached Impl gap remains at the cursor");
    debug_assert_eq!(leading.range(), start.leading.range());
    committed.emit_trivia(&leading);
    let keyword = committed
        .probe(|probe| probe.input().run(scan_word))
        .expect("the accepted Type-attached Impl keyword remains at the cursor");
    debug_assert_eq!(keyword.range(), start.keyword.range());
    debug_assert_eq!(keyword.text(), "impl");
    committed.token(SyntaxKind::ImplKw, keyword.range());
    commit_impl_tail(
        table,
        type_attached_impl_tail_owner_spec(start.type_base),
        committed,
    );
    let range = Recovered::Complete(keyword.range().start..committed_position(committed));
    committed.probe(|probe| probe.input().errors_rollback(errors_checkpoint));
    range
}

fn commit_impl_after_head<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    head_terminated_incomplete: bool,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        if !head_terminated_incomplete {
            emit_impl_tail_body_introducer_missing(owner_spec, committed);
        }
        return;
    }
    let description = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let result = mod_trivia(owner_spec.owner_base, i).and_then(|leading| {
            let colon = i.run(scan_punctuation).and_then(|punctuation| {
                (punctuation.kind() == PunctuationKind::Colon).then_some(punctuation.range())
            })?;
            let trailing = i.run(scan_trivia).expect("trivia scan is total");
            (!i.input.source()[trailing.range()].contains(['\r', '\n'])).then_some((leading, colon))
        });
        i.rollback(checkpoint);
        result
    });
    let Some((leading, colon)) = description else {
        commit_impl_body(table, owner_spec, committed, head_terminated_incomplete);
        return;
    };

    let consumed_leading = committed
        .probe(|probe| mod_trivia(owner_spec.owner_base, probe.input()))
        .expect("the shared description probe leaves its leading trivia at the cursor");
    assert_eq!(consumed_leading.range(), leading.range());
    committed.emit_trivia(&consumed_leading);
    committed.start_node(SyntaxKind::ImplDescription);
    let punctuation = committed
        .probe(|probe| probe.input().run(scan_punctuation))
        .expect("the isolated description probe leaves its colon at the cursor");
    assert_eq!(punctuation.range(), colon);
    committed.token(SyntaxKind::Colon, colon);
    let trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia scan is total");
    committed.emit_trivia(&trivia);
    let description = commit_required_impl_tail_type_expression(
        owner_spec,
        ImplTypeExpressionSlot::Description,
        committed,
    );
    committed.finish_node();
    commit_impl_body(
        table,
        owner_spec,
        committed,
        head_terminated_incomplete || matches!(description, Recovered::Incomplete),
    );
}

#[derive(Clone)]
enum ImplBodyStarter {
    Bodyless(Range<usize>),
    Braced(Range<usize>),
    Colon(Range<usize>),
}

fn commit_impl_body<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    upstream_slot_terminated_incomplete: bool,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        if !upstream_slot_terminated_incomplete {
            emit_impl_tail_body_introducer_missing(owner_spec, committed);
        }
        return;
    }
    let starter = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let starter = mod_trivia(owner_spec.owner_base, i).and_then(|trivia| {
            let punctuation = i.run(scan_punctuation)?;
            let starter = match punctuation.kind() {
                PunctuationKind::Semicolon => ImplBodyStarter::Bodyless(punctuation.range()),
                PunctuationKind::Open(Delimiter::Brace) => {
                    ImplBodyStarter::Braced(punctuation.range())
                }
                PunctuationKind::Colon => ImplBodyStarter::Colon(punctuation.range()),
                _ => return None,
            };
            Some((trivia, starter))
        });
        i.rollback(checkpoint);
        starter
    });
    let Some((trivia, starter)) = starter else {
        let trivia = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let trivia = mod_trivia(owner_spec.owner_base, i);
            i.rollback(checkpoint);
            trivia
        });
        let Some(trivia) = trivia else {
            if !upstream_slot_terminated_incomplete {
                emit_impl_tail_body_introducer_missing(owner_spec, committed);
            }
            return;
        };
        let newline = committed
            .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
        if newline {
            if !upstream_slot_terminated_incomplete {
                emit_impl_tail_body_introducer_missing(owner_spec, committed);
            }
            return;
        }
        let consumed_trivia = committed
            .probe(|probe| mod_trivia(owner_spec.owner_base, probe.input()))
            .expect("the Impl body-introducer recovery leaves its leading trivia at the cursor");
        assert_eq!(consumed_trivia.range(), trivia.range());
        committed.emit_trivia(&consumed_trivia);
        match impl_body_introducer_error_retry(owner_spec, committed) {
            Some(true) => {
                commit_impl_body(
                    table,
                    owner_spec,
                    committed,
                    upstream_slot_terminated_incomplete,
                );
            }
            Some(false) => {}
            None if !upstream_slot_terminated_incomplete => {
                emit_impl_tail_body_introducer_missing(owner_spec, committed)
            }
            None => {}
        }
        return;
    };
    let consumed_trivia = committed
        .probe(|probe| mod_trivia(owner_spec.owner_base, probe.input()))
        .expect("the accepted Impl body starter leaves its leading trivia at the cursor");
    assert_eq!(consumed_trivia.range(), trivia.range());
    committed.emit_trivia(&consumed_trivia);
    let punctuation = committed
        .probe(|probe| probe.input().run(scan_punctuation))
        .expect("the accepted Impl body starter remains at the cursor");
    match starter {
        ImplBodyStarter::Bodyless(range) => {
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Semicolon, range);
        }
        ImplBodyStarter::Braced(range) => {
            assert_eq!(punctuation.range(), range);
            commit_braced_statement_block_expression(table, range, committed);
        }
        ImplBodyStarter::Colon(range) => {
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Colon, range);
            commit_impl_colon_body(table, owner_spec, committed);
        }
    }
}

fn commit_impl_colon_body<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    let trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia scan is total");
    let newline = committed
        .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
    if newline
        && committed.probe(|probe| probe.input().local.line().line_indent <= owner_spec.owner_base)
    {
        committed.probe(|probe| probe.input().rollback(checkpoint));
        emit_impl_tail_body_missing(owner_spec, committed);
        return;
    }
    if newline {
        let block_indent = committed.probe(|probe| probe.input().local.line().line_indent);
        commit_indented_impl_tail_body(
            table,
            trivia,
            owner_spec.owner_base,
            block_indent,
            owner_spec.grammar_role(ImplRole::IndentedStatement),
            committed,
        );
        return;
    }
    committed.emit_trivia(&trivia);
    let ambient_scope = committed.probe(|probe| {
        probe
            .input()
            .local
            .push_inline_canonical_statement_ambient_scope(
                crate::session::InlineStatementOwnerKind::ImplColonBody,
            )
    });
    let statement_committed = if commit_canonical_statement(table, LeadingTrivia::None, committed) {
        true
    } else {
        match impl_body_error_retry(table, owner_spec, committed) {
            Some(true) => commit_canonical_statement(table, LeadingTrivia::None, committed),
            Some(false) => false,
            None => {
                emit_impl_tail_body_missing(owner_spec, committed);
                false
            }
        }
    };
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

fn impl_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Semicolon
                | PunctuationKind::Open(Delimiter::Brace)
                | PunctuationKind::Colon
        )
    });
    i.rollback(checkpoint);
    pending
}

fn impl_body_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Comma
                | PunctuationKind::Close(
                    Delimiter::Parenthesis | Delimiter::Bracket | Delimiter::Brace
                )
                | PunctuationKind::Open(Delimiter::Brace)
                | PunctuationKind::Colon
                | PunctuationKind::Semicolon
        )
    });
    i.rollback(checkpoint);
    pending
}

/// Consumes one malformed body-starter run until an actual Impl starter or a
/// caller-owned boundary.  The AST path consumes the same bytes without
/// emitting; direct CST realizes the one typed error record below.
fn impl_body_introducer_error_retry_ast<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if impl_body_starter_pending(i) {
            return (start < i.pos()).then_some(true);
        }
        if impl_body_boundary_pending(i) {
            return (start < i.pos()).then_some(false);
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < i.pos()).then_some(false);
        };
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn impl_body_error_retry_ast<'source, E>(
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
        if impl_body_boundary_pending(i) {
            return (start < i.pos()).then_some(false);
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < i.pos()).then_some(false);
        };
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        let checkpoint = i.checkpoint();
        let candidate = i
            .run(from_fn(|i| parse_canonical_statement(table, i)))
            .is_some();
        i.rollback(checkpoint);
        if candidate {
            return Some(true);
        }
    }
}

fn impl_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
    owner_spec: ImplTailOwnerSpec,
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
        loop {
            let i = probe.input();
            if impl_body_starter_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), true));
            }
            if impl_body_boundary_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            let Some(character) = i.input.remainder().chars().next() else {
                return (start < i.pos()).then_some((start..i.pos(), false));
            };
            if matches!(character, '\r' | '\n') {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            i.input.next()?;
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    })?;
    emit_impl_tail_error(
        owner_spec,
        committed,
        ImplRole::BodyIntroducer,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
        recovered.0,
    );
    Some(recovered.1)
}

fn impl_body_error_retry<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
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
        loop {
            {
                let i = probe.input();
                if impl_body_boundary_pending(i) {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                }
                let Some(character) = i.input.remainder().chars().next() else {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                };
                if matches!(character, '\r' | '\n') {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                }
                i.input.next()?;
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            if crate::grammar::expression::direct_canonical_statement_candidate(
                table,
                LeadingTrivia::None,
                probe,
            ) {
                let end = probe.input().pos();
                return Some((start..end, true));
            }
        }
    })?;
    emit_impl_tail_error(
        owner_spec,
        committed,
        ImplRole::Body,
        ExpectedSyntax::Statement,
        recovered.0,
    );
    Some(recovered.1)
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

/// The isolated raw Enum header shared by the later AST and direct-CST
/// declaration adapters. Enum names deliberately remain one raw word rather
/// than widening to a TypeExpression episode.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedEnumHeader<'source> {
    name: Recovered<WordSpan<'source>>,
    parameters: Vec<DeclarationTypeParameter<'source>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum EnumHeaderRecovery {
    Missing { at: usize },
    Error { range: Range<usize> },
}

/// Parses Enum's mandatory raw name and optional same-line generic list.
///
/// The accepted-intro boundary check happens before its gap is consumed. A
/// failed name stops this adapter immediately: derives and body ownership
/// remain for their later gates, without a cascade from the same cause.
#[allow(dead_code)]
fn parse_required_enum_header_isolated<'source, E>(
    intro: &EnumStatementIntro<'source>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (ParsedEnumHeader<'source>, Vec<EnumHeaderRecovery>)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut recoveries = Vec::new();
    let name_boundary = any_ambient_owner_claims(i);
    if !name_boundary {
        let _ = mod_trivia(intro.enum_base, i);
    }
    let name = if name_boundary {
        recoveries.push(EnumHeaderRecovery::Missing { at: i.pos() });
        Recovered::Incomplete
    } else if let Some(name) = i.run(scan_word) {
        Recovered::Complete(name)
    } else if let Some(recovery) = scan_enum_name_invalid_run(i) {
        recoveries.push(EnumHeaderRecovery::Error {
            range: recovery.range.clone(),
        });
        match recovery.target {
            EnumNameInvalidTarget::RawName => Recovered::Complete(
                i.run(scan_word)
                    .expect("an Enum name retry leaves its raw word at the cursor"),
            ),
            EnumNameInvalidTarget::BodyStarterOrBoundary => Recovered::Incomplete,
        }
    } else {
        recoveries.push(EnumHeaderRecovery::Missing { at: i.pos() });
        Recovered::Incomplete
    };
    let parameters = matches!(name, Recovered::Complete(_))
        .then(|| scan_declaration_type_parameter_list(i).unwrap_or_default())
        .unwrap_or_default();
    (ParsedEnumHeader { name, parameters }, recoveries)
}

/// Direct-CST's Enum header adapter scans the same decision stream, then
/// realizes only its raw surface and typed Name recovery records.
#[allow(dead_code)]
fn commit_required_enum_header_isolated<'parse, 'source, 'local, E, O>(
    intro: &EnumStatementIntro<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> ParsedEnumHeader<'source>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let (header, recoveries, header_end) = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let (header, recoveries) = parse_required_enum_header_isolated(intro, i);
        let end = i.pos();
        i.rollback(checkpoint);
        (header, recoveries, end)
    });
    commit_enum_header_surface(intro.enum_base, &header, &recoveries, header_end, committed);
    header
}

fn commit_enum_header_surface<'parse, 'source, 'local, E, O>(
    enum_base: usize,
    header: &ParsedEnumHeader<'source>,
    recoveries: &[EnumHeaderRecovery],
    header_end: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let name_target = recoveries
        .first()
        .map(enum_header_recovery_start)
        .or_else(|| match &header.name {
            Recovered::Complete(name) => Some(name.range().start),
            Recovered::Incomplete => None,
        })
        .unwrap_or(header_end);
    let current = committed.probe(|probe| probe.input().pos());
    if current < name_target {
        let trivia = committed
            .probe(|probe| mod_trivia(enum_base, probe.input()))
            .expect("the accepted Enum header gap remains declaration-continuing trivia");
        debug_assert_eq!(trivia.range(), current..name_target);
        committed.emit_trivia(&trivia);
    }
    if let Some(recovery) = recoveries.first() {
        commit_enum_header_recovery(recovery.clone(), committed);
    }
    if let Recovered::Complete(expected) = &header.name {
        let actual = commit_word(committed).expect("an accepted Enum name remains at the cursor");
        debug_assert_eq!(actual.range(), expected.range());
        committed.token(SyntaxKind::Identifier, actual.range());
    }
    if !header.parameters.is_empty() {
        committed.start_node(SyntaxKind::DeclarationTypeParameterList);
        for parameter in &header.parameters {
            let trivia = committed
                .probe(|probe| scan_required_inline_trivia(probe.input()))
                .expect("an accepted Enum parameter retains its same-line separator");
            committed.emit_trivia(&trivia);
            let actual = committed
                .probe(|probe| probe.input().run(scan_path_segment))
                .expect("an accepted Enum parameter remains at the cursor");
            debug_assert_eq!(actual.range(), declaration_type_parameter_range(parameter));
            committed.token(declaration_type_parameter_kind(parameter), actual.range());
        }
        committed.finish_node();
    }
    debug_assert_eq!(committed.probe(|probe| probe.input().pos()), header_end);
}

fn commit_enum_header_recovery<'parse, 'source, 'local, E, O>(
    recovery: EnumHeaderRecovery,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    if let EnumHeaderRecovery::Error { range } = &recovery {
        committed.probe(|probe| {
            let i = probe.input();
            debug_assert_eq!(i.pos(), range.start);
            while i.pos() < range.end {
                i.input
                    .next()
                    .expect("a selected Enum header error range remains available");
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            debug_assert_eq!(i.pos(), range.end);
        });
    }
    emit_enum_header_recovery(committed, recovery);
}

fn enum_header_recovery_start(recovery: &EnumHeaderRecovery) -> usize {
    match recovery {
        EnumHeaderRecovery::Missing { at } => *at,
        EnumHeaderRecovery::Error { range } => range.start,
    }
}

fn emit_enum_header_recovery<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    recovery: EnumHeaderRecovery,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let (kind, range, unexpected) = match recovery {
        EnumHeaderRecovery::Missing { at } => (RecoveryKind::Missing, at..at, Arc::from([])),
        EnumHeaderRecovery::Error { range } => {
            let unexpected = Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]);
            (RecoveryKind::Error, range, unexpected)
        }
    };
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Name));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            kind,
            unexpected,
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Identifier,
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
enum EnumNameInvalidTarget {
    RawName,
    BodyStarterOrBoundary,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct EnumNameInvalidRun {
    range: Range<usize>,
    target: EnumNameInvalidTarget,
}

fn scan_enum_name_invalid_run<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<EnumNameInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if enum_raw_name_pending(i) {
            return (start < i.pos()).then_some(EnumNameInvalidRun {
                range: start..i.pos(),
                target: EnumNameInvalidTarget::RawName,
            });
        }
        if enum_header_body_starter_or_boundary_pending(i) {
            return (start < i.pos()).then_some(EnumNameInvalidRun {
                range: start..i.pos(),
                target: EnumNameInvalidTarget::BodyStarterOrBoundary,
            });
        }
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(EnumNameInvalidRun {
                range: start..i.pos(),
                target: EnumNameInvalidTarget::BodyStarterOrBoundary,
            });
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn enum_raw_name_pending<E>(i: &mut SynIn<E>) -> bool
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

/// Variant heads have the same raw lexical candidate rule as the declaration
/// name, but keep a distinct helper so later payload code cannot accidentally
/// inherit header-only boundary policy.
fn enum_variant_raw_name_pending<E>(i: &mut SynIn<E>) -> bool
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

fn enum_header_body_starter_or_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty()
        || any_ambient_owner_claims(i)
        || declaration_exact_equals_pending(i)
    {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Semicolon
                | PunctuationKind::Open(Delimiter::Brace)
                | PunctuationKind::Colon,
        )
    });
    i.rollback(checkpoint);
    pending
}

/// The isolated raw Error header shared by the later AST and direct-CST
/// declaration adapters. Error names deliberately remain one raw word rather
/// than widening to a TypeExpression episode.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedErrorHeader<'source> {
    name: Recovered<WordSpan<'source>>,
    parameters: Vec<DeclarationTypeParameter<'source>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ErrorHeaderRecovery {
    Missing { at: usize },
    Error { range: Range<usize> },
}

/// Parses Error's mandatory raw name and optional same-line generic list.
///
/// The accepted-intro boundary check happens before its gap is consumed. A
/// failed name stops this adapter immediately: derives and body ownership
/// remain for their later gates, without a cascade from the same cause.
#[allow(dead_code)]
fn parse_required_error_header_isolated<'source, E>(
    intro: &ErrorStatementIntro<'source>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (ParsedErrorHeader<'source>, Vec<ErrorHeaderRecovery>)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut recoveries = Vec::new();
    let name_boundary = any_ambient_owner_claims(i);
    if !name_boundary {
        let _ = mod_trivia(intro.error_base, i);
    }
    let name = if name_boundary {
        recoveries.push(ErrorHeaderRecovery::Missing { at: i.pos() });
        Recovered::Incomplete
    } else if let Some(name) = i.run(scan_word) {
        Recovered::Complete(name)
    } else if let Some(recovery) = scan_error_name_invalid_run(i) {
        recoveries.push(ErrorHeaderRecovery::Error {
            range: recovery.range.clone(),
        });
        match recovery.target {
            ErrorNameInvalidTarget::RawName => Recovered::Complete(
                i.run(scan_word)
                    .expect("an Error name retry leaves its raw word at the cursor"),
            ),
            ErrorNameInvalidTarget::BodyStarterOrBoundary => Recovered::Incomplete,
        }
    } else {
        recoveries.push(ErrorHeaderRecovery::Missing { at: i.pos() });
        Recovered::Incomplete
    };
    let parameters = matches!(name, Recovered::Complete(_))
        .then(|| scan_declaration_type_parameter_list(i).unwrap_or_default())
        .unwrap_or_default();
    (ParsedErrorHeader { name, parameters }, recoveries)
}

/// Direct-CST's Error header adapter scans the same decision stream, then
/// realizes only its raw surface and typed Name recovery records.
#[allow(dead_code)]
fn commit_required_error_header_isolated<'parse, 'source, 'local, E, O>(
    intro: &ErrorStatementIntro<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> ParsedErrorHeader<'source>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let (header, recoveries, header_end) = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let (header, recoveries) = parse_required_error_header_isolated(intro, i);
        let end = i.pos();
        i.rollback(checkpoint);
        (header, recoveries, end)
    });
    commit_error_header_surface(
        intro.error_base,
        &header,
        &recoveries,
        header_end,
        committed,
    );
    header
}

fn commit_error_header_surface<'parse, 'source, 'local, E, O>(
    error_base: usize,
    header: &ParsedErrorHeader<'source>,
    recoveries: &[ErrorHeaderRecovery],
    header_end: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let name_target = recoveries
        .first()
        .map(error_header_recovery_start)
        .or_else(|| match &header.name {
            Recovered::Complete(name) => Some(name.range().start),
            Recovered::Incomplete => None,
        })
        .unwrap_or(header_end);
    let current = committed.probe(|probe| probe.input().pos());
    if current < name_target {
        let trivia = committed
            .probe(|probe| mod_trivia(error_base, probe.input()))
            .expect("the accepted Error header gap remains declaration-continuing trivia");
        debug_assert_eq!(trivia.range(), current..name_target);
        committed.emit_trivia(&trivia);
    }
    if let Some(recovery) = recoveries.first() {
        commit_error_header_recovery(recovery.clone(), committed);
    }
    if let Recovered::Complete(expected) = &header.name {
        let actual = commit_word(committed).expect("an accepted Error name remains at the cursor");
        debug_assert_eq!(actual.range(), expected.range());
        committed.token(SyntaxKind::Identifier, actual.range());
    }
    if !header.parameters.is_empty() {
        committed.start_node(SyntaxKind::DeclarationTypeParameterList);
        for parameter in &header.parameters {
            let trivia = committed
                .probe(|probe| scan_required_inline_trivia(probe.input()))
                .expect("an accepted Error parameter retains its same-line separator");
            committed.emit_trivia(&trivia);
            let actual = committed
                .probe(|probe| probe.input().run(scan_path_segment))
                .expect("an accepted Error parameter remains at the cursor");
            debug_assert_eq!(actual.range(), declaration_type_parameter_range(parameter));
            committed.token(declaration_type_parameter_kind(parameter), actual.range());
        }
        committed.finish_node();
    }
    debug_assert_eq!(committed.probe(|probe| probe.input().pos()), header_end);
}

fn commit_error_header_recovery<'parse, 'source, 'local, E, O>(
    recovery: ErrorHeaderRecovery,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    if let ErrorHeaderRecovery::Error { range } = &recovery {
        committed.probe(|probe| {
            let i = probe.input();
            debug_assert_eq!(i.pos(), range.start);
            while i.pos() < range.end {
                i.input
                    .next()
                    .expect("a selected Error header error range remains available");
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            debug_assert_eq!(i.pos(), range.end);
        });
    }
    emit_error_header_recovery(committed, recovery);
}

fn error_header_recovery_start(recovery: &ErrorHeaderRecovery) -> usize {
    match recovery {
        ErrorHeaderRecovery::Missing { at } => *at,
        ErrorHeaderRecovery::Error { range } => range.start,
    }
}

fn emit_error_header_recovery<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    recovery: ErrorHeaderRecovery,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let (kind, range, unexpected) = match recovery {
        ErrorHeaderRecovery::Missing { at } => (RecoveryKind::Missing, at..at, Arc::from([])),
        ErrorHeaderRecovery::Error { range } => {
            let unexpected = Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]);
            (RecoveryKind::Error, range, unexpected)
        }
    };
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Name));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            kind,
            unexpected,
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Identifier,
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
enum ErrorNameInvalidTarget {
    RawName,
    BodyStarterOrBoundary,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ErrorNameInvalidRun {
    range: Range<usize>,
    target: ErrorNameInvalidTarget,
}

fn scan_error_name_invalid_run<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<ErrorNameInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if error_raw_name_pending(i) {
            return (start < i.pos()).then_some(ErrorNameInvalidRun {
                range: start..i.pos(),
                target: ErrorNameInvalidTarget::RawName,
            });
        }
        if error_header_body_starter_or_boundary_pending(i) {
            return (start < i.pos()).then_some(ErrorNameInvalidRun {
                range: start..i.pos(),
                target: ErrorNameInvalidTarget::BodyStarterOrBoundary,
            });
        }
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(ErrorNameInvalidRun {
                range: start..i.pos(),
                target: ErrorNameInvalidTarget::BodyStarterOrBoundary,
            });
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn error_raw_name_pending<E>(i: &mut SynIn<E>) -> bool
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

fn error_header_body_starter_or_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty()
        || any_ambient_owner_claims(i)
        || declaration_exact_equals_pending(i)
    {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Semicolon
                | PunctuationKind::Open(Delimiter::Brace)
                | PunctuationKind::Colon,
        )
    });
    i.rollback(checkpoint);
    pending
}

/// The four body-local separator regimes share one stream judge.  The form
/// controls only separator and terminal authority; variant head and payload
/// parsing deliberately stay behind [`VariantDeclarationSequenceContext`] until Gate
/// 6 supplies their real AST/direct-CST adapters.
#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum VariantDeclarationSequenceForm {
    Braced,
    ColonIndented,
    EqualsInline,
    EqualsIndented,
}

/// Backward-compatible fixture spelling for the neutral sequence-form type.
/// Production adapters use `VariantDeclarationSequenceForm` directly.
type EnumVariantSequenceForm = VariantDeclarationSequenceForm;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct EnumVariantSeparatorSet {
    comma: bool,
    pipe: bool,
}

impl EnumVariantSeparatorSet {
    #[allow(dead_code)]
    const fn new(comma: bool, pipe: bool) -> Self {
        Self { comma, pipe }
    }
}

/// The invariant sequence inputs selected by the body-form judge.  In
/// particular, the layout frame is captured by that owner once; a later
/// variant or recovery path must never reconstruct it from an item.
#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct VariantDeclarationSequenceSpec {
    form: VariantDeclarationSequenceForm,
    layout: LayoutDelimitedFrame,
    declaration_base: usize,
    explicit_separators: EnumVariantSeparatorSet,
    matching_close: Option<Delimiter>,
    allow_leading_pipe: bool,
    allow_trailing_pipe: bool,
}

/// Backward-compatible fixture spelling for the neutral sequence spec.
/// Production adapters use `VariantDeclarationSequenceSpec` directly.
type EnumVariantSequenceSpec = VariantDeclarationSequenceSpec;

#[derive(Clone, Debug, Eq, PartialEq)]
enum EnumVariantSeparator {
    Comma(Range<usize>),
    Pipe(Range<usize>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum EnumVariantSequenceTermination {
    MatchingClose(Range<usize>),
    MismatchedClose,
    Dedent,
    OwnerBoundary,
    EndOfInput,
    ItemContinuation,
}

/// Item realization is intentionally the only pluggable part of the neutral
/// stream.  Gate 5's fixture context consumes one raw word; Gate 6 will make
/// the same callback own `from`, named, tuple, and positional payloads.
trait VariantDeclarationSequenceContext<'source> {
    type Error: ErrorSink<usize>;

    fn with_input<R>(&mut self, f: impl FnOnce(&mut SynIn<'_, 'source, '_, Self::Error>) -> R)
    -> R;
    fn emit_trivia(&mut self, trivia: &TriviaRun);
    fn emit_missing_variant(&mut self);
    fn emit_separator(&mut self, separator: EnumVariantSeparator);
    fn set_trailing_separator(&mut self, separator: EnumVariantSeparator);
    fn emit_matching_close(&mut self, close: Range<usize>);

    /// Receives an already-selected malformed prefix, if any, with the cursor
    /// at its raw-name retry candidate or at a terminal safe point.  Returning
    /// false closes one incomplete item without making the stream invent a
    /// second recovery record.
    fn parse_variant_item(&mut self, malformed: Option<Range<usize>>) -> bool;
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum EnumVariantSequencePosition {
    Optional,
    Required {
        pending_boundary: Option<EnumVariantBoundary>,
    },
    AfterVariant,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum EnumVariantBoundary {
    Explicit(EnumVariantSeparator),
    LayoutNewline,
}

#[derive(Clone, Debug)]
struct EnumVariantSequenceState {
    position: EnumVariantSequencePosition,
    accepted_variant: bool,
    accepted_leading_pipe: bool,
}

impl EnumVariantSequenceState {
    fn new(spec: EnumVariantSequenceSpec) -> Self {
        let position = if matches!(spec.form, EnumVariantSequenceForm::Braced) {
            EnumVariantSequencePosition::Optional
        } else {
            EnumVariantSequencePosition::Required {
                pending_boundary: None,
            }
        };
        Self {
            position,
            accepted_variant: false,
            accepted_leading_pipe: false,
        }
    }

    fn accepted_variant(&mut self) {
        self.position = EnumVariantSequencePosition::AfterVariant;
        self.accepted_variant = true;
    }

    fn qualifying_newline(&mut self) {
        if matches!(self.position, EnumVariantSequencePosition::AfterVariant) {
            self.position = EnumVariantSequencePosition::Required {
                pending_boundary: Some(EnumVariantBoundary::LayoutNewline),
            };
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EnumVariantJudgeOrigin {
    FreshSlot,
    Continuation,
}

enum EnumVariantGap {
    SameLine(TriviaRun),
    QualifyingNewline(TriviaRun),
    Dedent,
    Owner,
    ItemContinuation,
    None,
}

struct EnumVariantSeparatorCluster {
    trivia: TriviaRun,
    separator: EnumVariantSeparator,
}

/// Drives only sequence evidence.  A raw word following a completed stub item
/// on the same line is deliberately returned as [`ItemContinuation`] rather
/// than guessed to be a second variant: Gate 6 owns its positional payload.
#[allow(dead_code)]
fn drive_variant_declaration_sequence<'source, C>(
    context: &mut C,
    spec: VariantDeclarationSequenceSpec,
) -> EnumVariantSequenceTermination
where
    C: VariantDeclarationSequenceContext<'source>,
    Unexpected<char>: Into<<C::Error as ErrorSink<usize>>::Error>,
    UnexpectedEndOfInput: Into<<C::Error as ErrorSink<usize>>::Error>,
{
    let mut state = EnumVariantSequenceState::new(spec);
    let mut origin = EnumVariantJudgeOrigin::FreshSlot;

    loop {
        if context.with_input(|i| i.input.remainder().is_empty()) {
            finish_enum_variant_sequence(&mut state, spec, context);
            return EnumVariantSequenceTermination::EndOfInput;
        }
        if let Some(close) = context.with_input(|i| scan_enum_variant_matching_close(spec, i)) {
            finish_enum_variant_sequence(&mut state, spec, context);
            context.emit_matching_close(close.clone());
            return EnumVariantSequenceTermination::MatchingClose(close);
        }
        if context.with_input(|i| enum_variant_mismatched_close_pending(spec, i)) {
            finish_enum_variant_sequence(&mut state, spec, context);
            return EnumVariantSequenceTermination::MismatchedClose;
        }
        if let Some(cluster) = context.with_input(|i| scan_enum_variant_separator_cluster(spec, i))
        {
            apply_enum_variant_separator(&mut state, spec, &cluster.separator, context);
            if !cluster.trivia.is_empty() {
                context.emit_trivia(&cluster.trivia);
            }
            context.emit_separator(cluster.separator);
            origin = EnumVariantJudgeOrigin::FreshSlot;
            continue;
        }
        if matches!(origin, EnumVariantJudgeOrigin::Continuation)
            && context.with_input(any_ambient_owner_claims)
        {
            finish_enum_variant_sequence(&mut state, spec, context);
            return EnumVariantSequenceTermination::OwnerBoundary;
        }

        match context.with_input(|i| classify_enum_variant_gap(spec, i)) {
            EnumVariantGap::SameLine(trivia) => {
                let terminal_follows = context
                    .with_input(|i| enum_variant_same_line_trivia_precedes_terminal(spec, i));
                if matches!(origin, EnumVariantJudgeOrigin::FreshSlot) || terminal_follows {
                    let consumed = context.with_input(consume_enum_variant_trivia);
                    debug_assert_eq!(consumed.range(), trivia.range());
                    context.emit_trivia(&consumed);
                    continue;
                }
                return EnumVariantSequenceTermination::ItemContinuation;
            }
            EnumVariantGap::QualifyingNewline(trivia) => {
                let consumed = context.with_input(consume_enum_variant_trivia);
                debug_assert_eq!(consumed.range(), trivia.range());
                context.emit_trivia(&consumed);
                state.qualifying_newline();
                origin = EnumVariantJudgeOrigin::FreshSlot;
                continue;
            }
            EnumVariantGap::Dedent => {
                finish_enum_variant_sequence(&mut state, spec, context);
                return EnumVariantSequenceTermination::Dedent;
            }
            EnumVariantGap::Owner => {
                finish_enum_variant_sequence(&mut state, spec, context);
                return EnumVariantSequenceTermination::OwnerBoundary;
            }
            EnumVariantGap::ItemContinuation => {
                return EnumVariantSequenceTermination::ItemContinuation;
            }
            EnumVariantGap::None => {}
        }

        if context.with_input(|i| enum_variant_terminal_boundary_pending(spec, i)) {
            finish_enum_variant_sequence(&mut state, spec, context);
            return if context.with_input(|i| i.input.remainder().is_empty()) {
                EnumVariantSequenceTermination::EndOfInput
            } else {
                EnumVariantSequenceTermination::OwnerBoundary
            };
        }
        if context.with_input(enum_variant_raw_name_pending) {
            if !context.parse_variant_item(None) {
                return EnumVariantSequenceTermination::ItemContinuation;
            }
            state.accepted_variant();
            origin = EnumVariantJudgeOrigin::Continuation;
            continue;
        }
        if let Some(range) = context.with_input(|i| scan_enum_variant_invalid_run(spec, i)) {
            let _retried = context.parse_variant_item(Some(range));
            state.accepted_variant();
            origin = EnumVariantJudgeOrigin::Continuation;
            continue;
        }

        finish_enum_variant_sequence(&mut state, spec, context);
        return EnumVariantSequenceTermination::ItemContinuation;
    }
}

/// The former Enum-named entry point remains only for Gate 5's existing
/// neutral sequence fixture; declaration adapters call the renamed core.
#[allow(dead_code)]
fn drive_enum_variant_sequence<'source, C>(
    context: &mut C,
    spec: VariantDeclarationSequenceSpec,
) -> EnumVariantSequenceTermination
where
    C: VariantDeclarationSequenceContext<'source>,
    Unexpected<char>: Into<<C::Error as ErrorSink<usize>>::Error>,
    UnexpectedEndOfInput: Into<<C::Error as ErrorSink<usize>>::Error>,
{
    drive_variant_declaration_sequence(context, spec)
}

fn apply_enum_variant_separator<'source, C>(
    state: &mut EnumVariantSequenceState,
    spec: EnumVariantSequenceSpec,
    separator: &EnumVariantSeparator,
    context: &mut C,
) where
    C: VariantDeclarationSequenceContext<'source>,
{
    let pending_layout_pipe = matches!(
        (&state.position, separator),
        (
            EnumVariantSequencePosition::Required {
                pending_boundary: Some(EnumVariantBoundary::LayoutNewline),
            },
            EnumVariantSeparator::Pipe(_),
        )
    );
    let leading_pipe = matches!(separator, EnumVariantSeparator::Pipe(_))
        && spec.allow_leading_pipe
        && !state.accepted_variant
        && !state.accepted_leading_pipe
        && matches!(
            state.position,
            EnumVariantSequencePosition::Optional
                | EnumVariantSequencePosition::Required {
                    pending_boundary: None | Some(EnumVariantBoundary::LayoutNewline),
                }
        );
    if leading_pipe {
        state.accepted_leading_pipe = true;
    } else if !pending_layout_pipe
        && !matches!(state.position, EnumVariantSequencePosition::AfterVariant)
    {
        context.emit_missing_variant();
    }
    state.position = EnumVariantSequencePosition::Required {
        pending_boundary: Some(EnumVariantBoundary::Explicit(separator.clone())),
    };
}

fn finish_enum_variant_sequence<'source, C>(
    state: &mut EnumVariantSequenceState,
    spec: EnumVariantSequenceSpec,
    context: &mut C,
) where
    C: VariantDeclarationSequenceContext<'source>,
{
    let EnumVariantSequencePosition::Required { pending_boundary } = &state.position else {
        return;
    };
    match pending_boundary {
        Some(EnumVariantBoundary::Explicit(EnumVariantSeparator::Comma(_)))
        | Some(EnumVariantBoundary::LayoutNewline) => {
            if let Some(EnumVariantBoundary::Explicit(separator)) = pending_boundary {
                context.set_trailing_separator(separator.clone());
            }
        }
        Some(EnumVariantBoundary::Explicit(separator @ EnumVariantSeparator::Pipe(_)))
            if state.accepted_variant && spec.allow_trailing_pipe =>
        {
            context.set_trailing_separator(separator.clone());
        }
        _ => context.emit_missing_variant(),
    }
}

fn classify_enum_variant_gap<E>(spec: EnumVariantSequenceSpec, i: &mut SynIn<E>) -> EnumVariantGap
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return EnumVariantGap::Owner;
    }
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    if trivia.is_empty() {
        i.rollback(checkpoint);
        return EnumVariantGap::None;
    }
    if !enum_variant_trivia_has_newline(&trivia) {
        i.rollback(checkpoint);
        return EnumVariantGap::SameLine(trivia);
    }
    if matches!(spec.form, EnumVariantSequenceForm::EqualsInline) {
        i.rollback(checkpoint);
        return EnumVariantGap::ItemContinuation;
    }
    let following_indent = i.local.line().line_indent;
    if matches!(
        spec.form,
        EnumVariantSequenceForm::ColonIndented | EnumVariantSequenceForm::EqualsIndented
    ) && following_indent < spec.layout.base_indent()
    {
        i.rollback(checkpoint);
        return EnumVariantGap::Dedent;
    }
    let boundary = spec.layout.boundary_after_trivia(&trivia, following_indent);
    i.rollback(checkpoint);
    match boundary {
        LayoutDelimitedBoundary::ImplicitNewline => EnumVariantGap::QualifyingNewline(trivia),
        LayoutDelimitedBoundary::DeeperNewline => EnumVariantGap::ItemContinuation,
        LayoutDelimitedBoundary::None => EnumVariantGap::SameLine(trivia),
    }
}

fn scan_enum_variant_separator_cluster<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> Option<EnumVariantSeparatorCluster>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    if matches!(spec.form, EnumVariantSequenceForm::EqualsInline)
        && enum_variant_trivia_has_newline(&trivia)
    {
        i.rollback(checkpoint);
        return None;
    }
    let Some(separator) = scan_enum_variant_separator_at_cursor(spec, i) else {
        i.rollback(checkpoint);
        return None;
    };
    Some(EnumVariantSeparatorCluster { trivia, separator })
}

fn scan_enum_variant_separator_at_cursor<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> Option<EnumVariantSeparator>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if spec.explicit_separators.comma {
        let checkpoint = i.checkpoint();
        if let Some(punctuation) = i.run(scan_punctuation)
            && punctuation.kind() == PunctuationKind::Comma
        {
            return Some(EnumVariantSeparator::Comma(punctuation.range()));
        }
        i.rollback(checkpoint);
    }
    if spec.explicit_separators.pipe {
        let checkpoint = i.checkpoint();
        let start = i.pos();
        if i.skip(item('|')).is_some() {
            return Some(EnumVariantSeparator::Pipe(start..i.pos()));
        }
        i.rollback(checkpoint);
    }
    None
}

fn enum_variant_separator_pending<E>(spec: EnumVariantSequenceSpec, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_enum_variant_separator_at_cursor(spec, i).is_some();
    i.rollback(checkpoint);
    pending
}

fn scan_enum_variant_matching_close<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let delimiter = spec.matching_close?;
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() == PunctuationKind::Close(delimiter) {
        Some(punctuation.range())
    } else {
        i.rollback(checkpoint);
        None
    }
}

fn enum_variant_matching_close_pending<E>(spec: EnumVariantSequenceSpec, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_enum_variant_matching_close(spec, i).is_some();
    i.rollback(checkpoint);
    pending
}

fn enum_variant_mismatched_close_pending<E>(spec: EnumVariantSequenceSpec, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let Some(expected) = spec.matching_close else {
        return false;
    };
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(punctuation.kind(), PunctuationKind::Close(found) if found != expected)
    });
    i.rollback(checkpoint);
    pending
}

fn enum_variant_terminal_boundary_pending<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty() || any_ambient_owner_claims(i) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = i
        .run(scan_punctuation)
        .is_some_and(|punctuation| match punctuation.kind() {
            PunctuationKind::Semicolon | PunctuationKind::Close(_) => true,
            PunctuationKind::Comma => !spec.explicit_separators.comma,
            _ => false,
        });
    i.rollback(checkpoint);
    pending
}

fn enum_variant_same_line_trivia_precedes_terminal<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    let terminal = !trivia.is_empty()
        && !enum_variant_trivia_has_newline(&trivia)
        && (scan_enum_variant_matching_close(spec, i).is_some()
            || enum_variant_mismatched_close_pending(spec, i)
            || enum_variant_terminal_boundary_pending(spec, i));
    i.rollback(checkpoint);
    terminal
}

fn scan_enum_variant_invalid_run<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if enum_variant_raw_name_pending(i)
            || enum_variant_matching_close_pending(spec, i)
            || enum_variant_mismatched_close_pending(spec, i)
            || enum_variant_terminal_boundary_pending(spec, i)
            || enum_variant_separator_pending(spec, i)
        {
            return (start < i.pos()).then_some(start..i.pos());
        }
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(start..i.pos());
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn consume_enum_variant_trivia<E>(i: &mut SynIn<E>) -> TriviaRun
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.run(scan_trivia).expect("trivia scanning is total")
}

fn enum_variant_trivia_has_newline(trivia: &TriviaRun) -> bool {
    trivia
        .parts()
        .iter()
        .any(|part| matches!(part.kind(), TriviaPartKind::Newline))
}

/// The field grammar is structurally shared by Struct and Enum payloads, but
/// its recovery identity is owned by the surrounding declaration.  Keeping
/// that mapping explicit prevents an Enum payload from fabricating a Struct
/// recovery record while preserving Struct's existing public surface.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum VariantFieldDriverSpec {
    Struct,
    EnumNamed,
    EnumTuple,
    ErrorNamed,
    ErrorTuple,
}

impl VariantFieldDriverSpec {
    fn named_type_owner(self) -> TypeDelimitedOwner {
        match self {
            Self::Struct => TypeDelimitedOwner::StructNamedFields,
            Self::EnumNamed => TypeDelimitedOwner::VariantNamedPayload,
            Self::EnumTuple => TypeDelimitedOwner::VariantTuplePayload,
            Self::ErrorNamed => TypeDelimitedOwner::VariantNamedPayload,
            Self::ErrorTuple => TypeDelimitedOwner::VariantTuplePayload,
        }
    }

    fn type_role(self) -> GrammarRole {
        match self {
            Self::Struct => GrammarRole::Declaration(DeclarationRole::Struct(
                crate::session::StructRole::FieldType,
            )),
            Self::EnumNamed => GrammarRole::Declaration(DeclarationRole::Enum(
                EnumDeclarationRole::Variant(VariantDeclarationRole::NamedFieldType),
            )),
            Self::EnumTuple => GrammarRole::Declaration(DeclarationRole::Enum(
                EnumDeclarationRole::Variant(VariantDeclarationRole::TupleFieldType),
            )),
            Self::ErrorNamed => GrammarRole::Declaration(DeclarationRole::Error(
                ErrorDeclarationRole::Variant(VariantDeclarationRole::NamedFieldType),
            )),
            Self::ErrorTuple => GrammarRole::Declaration(DeclarationRole::Error(
                ErrorDeclarationRole::Variant(VariantDeclarationRole::TupleFieldType),
            )),
        }
    }

    fn tuple_payload(self) -> Self {
        match self {
            Self::EnumNamed | Self::EnumTuple => Self::EnumTuple,
            Self::ErrorNamed | Self::ErrorTuple => Self::ErrorTuple,
            Self::Struct => Self::Struct,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum VariantDeclarationOwner {
    Enum,
    Error,
}

/// The sole owner-specific input to the otherwise neutral variant sequence
/// and payload core. Form, layout, separators, and close authority remain in
/// `VariantDeclarationSequenceSpec`; this spec changes only recovery owners.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct VariantDeclarationOwnerSpec {
    owner: VariantDeclarationOwner,
    declaration_base: usize,
    item_role: GrammarRole,
    from_type_role: GrammarRole,
    positional_payload_role: GrammarRole,
    field_driver: VariantFieldDriverSpec,
}

impl VariantDeclarationOwnerSpec {
    fn variant_role(self, role: VariantDeclarationRole) -> GrammarRole {
        match self.owner {
            VariantDeclarationOwner::Enum => {
                GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Variant(role)))
            }
            VariantDeclarationOwner::Error => GrammarRole::Declaration(DeclarationRole::Error(
                ErrorDeclarationRole::Variant(role),
            )),
        }
    }
}

fn enum_variant_declaration_owner_spec(declaration_base: usize) -> VariantDeclarationOwnerSpec {
    VariantDeclarationOwnerSpec {
        owner: VariantDeclarationOwner::Enum,
        declaration_base,
        item_role: GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Variant(
            VariantDeclarationRole::Item,
        ))),
        from_type_role: GrammarRole::Declaration(DeclarationRole::Enum(
            EnumDeclarationRole::Variant(VariantDeclarationRole::FromType),
        )),
        positional_payload_role: GrammarRole::Declaration(DeclarationRole::Enum(
            EnumDeclarationRole::Variant(VariantDeclarationRole::PositionalPayload),
        )),
        field_driver: VariantFieldDriverSpec::EnumNamed,
    }
}

fn error_variant_declaration_owner_spec(declaration_base: usize) -> VariantDeclarationOwnerSpec {
    VariantDeclarationOwnerSpec {
        owner: VariantDeclarationOwner::Error,
        declaration_base,
        item_role: GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Variant(
            VariantDeclarationRole::Item,
        ))),
        from_type_role: GrammarRole::Declaration(DeclarationRole::Error(
            ErrorDeclarationRole::Variant(VariantDeclarationRole::FromType),
        )),
        positional_payload_role: GrammarRole::Declaration(DeclarationRole::Error(
            ErrorDeclarationRole::Variant(VariantDeclarationRole::PositionalPayload),
        )),
        field_driver: VariantFieldDriverSpec::ErrorNamed,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EnumVariantTypeExpressionSlot {
    FromType,
    PositionalPayload,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct EnumVariantTypeExpressionEpisodeSpec {
    stops: StopSet,
    scoped_frame: TypeExpressionScopedStopFrame,
    policy: TypeExpressionEpisodePolicy,
    outer_role: GrammarRole,
    outer_ml_arg: bool,
}

/// Builds the one outer episode that owns an Enum payload item.  The scoped
/// frame deliberately makes the Enum separator visible only at this item's
/// completed-tail and malformed-safe points; nested TypeExpression episodes
/// keep the same raw stop bits but do not inherit that ownership.
fn variant_declaration_type_expression_episode_spec(
    owner: VariantDeclarationOwnerSpec,
    slot: EnumVariantTypeExpressionSlot,
    form: VariantDeclarationSequenceForm,
    incoming: StopSet,
    current_episode_depth: usize,
) -> EnumVariantTypeExpressionEpisodeSpec {
    let scoped_stops = match form {
        EnumVariantSequenceForm::Braced => StopSet::default()
            .with(StopKind::Comma)
            .with(StopKind::RightBrace),
        EnumVariantSequenceForm::EqualsInline => StopSet::default().with(StopKind::Pipe),
        EnumVariantSequenceForm::ColonIndented | EnumVariantSequenceForm::EqualsIndented => {
            StopSet::default()
                .with(StopKind::Comma)
                .with(StopKind::Pipe)
                .with(StopKind::Newline)
        }
    };
    let outer_role = match slot {
        EnumVariantTypeExpressionSlot::FromType => owner.from_type_role,
        EnumVariantTypeExpressionSlot::PositionalPayload => owner.positional_payload_role,
    };
    let stops = match form {
        EnumVariantSequenceForm::Braced => {
            incoming.with(StopKind::Comma).with(StopKind::RightBrace)
        }
        EnumVariantSequenceForm::EqualsInline => incoming.with(StopKind::Pipe),
        EnumVariantSequenceForm::ColonIndented | EnumVariantSequenceForm::EqualsIndented => {
            incoming
                .with(StopKind::Comma)
                .with(StopKind::Pipe)
                .with(StopKind::Newline)
        }
    };
    EnumVariantTypeExpressionEpisodeSpec {
        stops,
        scoped_frame: TypeExpressionScopedStopFrame {
            stops: scoped_stops,
            visible_episode_depth: current_episode_depth + 1,
        },
        policy: TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops: StopSet::default(),
            fresh_primary_owns_adjacent_polymorphic_variant_starter: true,
        },
        outer_role,
        outer_ml_arg: matches!(slot, EnumVariantTypeExpressionSlot::PositionalPayload),
    }
}

/// Tuple fields are owned by their local parenthesized field frame, not by an
/// outer Enum variant-payload slot.  Their scoped stops therefore name only
/// the local comma and matching parenthesis while preserving outer stops
/// underneath for the enclosing field-loop close handoff.
fn variant_declaration_tuple_field_type_expression_episode_spec(
    field_driver: VariantFieldDriverSpec,
    incoming: StopSet,
    current_episode_depth: usize,
) -> EnumVariantTypeExpressionEpisodeSpec {
    let scoped_stops = StopSet::default()
        .with(StopKind::Comma)
        .with(StopKind::RightParenthesis);
    let stops = incoming
        .with(StopKind::Comma)
        .with(StopKind::RightParenthesis);
    EnumVariantTypeExpressionEpisodeSpec {
        stops,
        scoped_frame: TypeExpressionScopedStopFrame {
            stops: scoped_stops,
            visible_episode_depth: current_episode_depth + 1,
        },
        policy: TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops: StopSet::default(),
            fresh_primary_owns_adjacent_polymorphic_variant_starter: true,
        },
        outer_role: field_driver.tuple_payload().type_role(),
        outer_ml_arg: false,
    }
}

fn parse_required_variant_declaration_type_expression<'source, E>(
    owner: VariantDeclarationOwnerSpec,
    slot: EnumVariantTypeExpressionSlot,
    form: VariantDeclarationSequenceForm,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = variant_declaration_type_expression_episode_spec(
        owner,
        slot,
        form,
        i.local.stop_set().unwrap_or_default(),
        i.local.type_expression_episode_depth(),
    );
    i.local.push_stop_set(episode.stops);
    i.local
        .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    let saved_ml_arg = i.local.type_ml_arg();
    i.local.set_type_ml_arg(episode.outer_ml_arg);
    let parsed = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_outer_missing_role_and_policy(
                    Some(episode.outer_role),
                    episode.policy,
                    i,
                ),
            )
        }))
        .expect("the mandatory Enum payload TypeExpression entry is total");
    i.local.set_type_ml_arg(saved_ml_arg);
    assert_eq!(
        i.local.pop_type_expression_scoped_stop_frame(),
        Some(episode.scoped_frame),
    );
    assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    match parsed {
        Recovered::Complete(parsed) => Recovered::Complete(Box::new(parsed)),
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

fn commit_required_variant_declaration_type_expression<'parse, 'source, 'local, E, O>(
    owner: VariantDeclarationOwnerSpec,
    slot: EnumVariantTypeExpressionSlot,
    form: VariantDeclarationSequenceForm,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = committed.probe(|probe| {
        let i = probe.input();
        variant_declaration_type_expression_episode_spec(
            owner,
            slot,
            form,
            i.local.stop_set().unwrap_or_default(),
            i.local.type_expression_episode_depth(),
        )
    });
    let saved_ml_arg = committed.probe(|probe| probe.input().local.type_ml_arg());
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(episode.stops);
        i.local
            .push_type_expression_scoped_stop_frame(episode.scoped_frame);
        i.local.set_type_ml_arg(episode.outer_ml_arg);
    });
    let parsed = commit_direct_type_expression_with_outer_missing_role_and_policy(
        Some(episode.outer_role),
        episode.policy,
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        i.local.set_type_ml_arg(saved_ml_arg);
        assert_eq!(
            i.local.pop_type_expression_scoped_stop_frame(),
            Some(episode.scoped_frame),
        );
        assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    });
    let range = parsed.range();
    if range.is_empty() {
        Recovered::Incomplete
    } else {
        Recovered::Complete(range)
    }
}

fn parse_required_variant_declaration_tuple_field_type_expression<'source, E>(
    field_driver: VariantFieldDriverSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = variant_declaration_tuple_field_type_expression_episode_spec(
        field_driver,
        i.local.stop_set().unwrap_or_default(),
        i.local.type_expression_episode_depth(),
    );
    i.local.push_stop_set(episode.stops);
    i.local
        .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    let parsed = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_outer_missing_role_and_policy(
                    Some(episode.outer_role),
                    episode.policy,
                    i,
                ),
            )
        }))
        .expect("mandatory Enum tuple field TypeExpression is total");
    assert_eq!(
        i.local.pop_type_expression_scoped_stop_frame(),
        Some(episode.scoped_frame),
    );
    assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    match parsed {
        Recovered::Complete(parsed) => Recovered::Complete(Box::new(parsed)),
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

fn commit_required_variant_declaration_tuple_field_type_expression<'parse, 'source, 'local, E, O>(
    field_driver: VariantFieldDriverSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = committed.probe(|probe| {
        let i = probe.input();
        variant_declaration_tuple_field_type_expression_episode_spec(
            field_driver,
            i.local.stop_set().unwrap_or_default(),
            i.local.type_expression_episode_depth(),
        )
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(episode.stops);
        i.local
            .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    });
    let parsed = commit_direct_type_expression_with_outer_missing_role_and_policy(
        Some(episode.outer_role),
        episode.policy,
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(
            i.local.pop_type_expression_scoped_stop_frame(),
            Some(episode.scoped_frame),
        );
        assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    });
    let range = parsed.range();
    if range.is_empty() {
        Recovered::Incomplete
    } else {
        Recovered::Complete(range)
    }
}

fn enum_variant_type_primary_pending<E>(i: &mut SynIn<E>) -> bool
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

/// After the higher-priority `from` and delimiter forms have declined, every
/// non-boundary byte after a payload gap is positional-payload evidence.  The
/// mandatory TypeExpression entry then owns its malformed-run retry; treating
/// that byte as the next Enum item would split one malformed payload across
/// two recovery owners.
fn enum_variant_positional_payload_pending<E>(
    form: EnumVariantSequenceForm,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if enum_variant_type_primary_pending(i) {
        return true;
    }
    if i.input.remainder().is_empty() || any_ambient_owner_claims(i) {
        return false;
    }
    if matches!(i.input.remainder().chars().next(), Some('\r' | '\n')) {
        return false;
    }
    let checkpoint = i.checkpoint();
    let punctuation = i
        .run(scan_punctuation)
        .map(|punctuation| punctuation.kind());
    i.rollback(checkpoint);
    !matches!(
        punctuation,
        Some(PunctuationKind::Comma | PunctuationKind::Semicolon | PunctuationKind::Close(_))
    ) && !(matches!(
        form,
        EnumVariantSequenceForm::EqualsInline
            | EnumVariantSequenceForm::ColonIndented
            | EnumVariantSequenceForm::EqualsIndented
    ) && i.input.remainder().starts_with('|'))
}

fn consume_enum_variant_payload_trivia<E>(i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    if trivia.is_empty() || enum_variant_trivia_has_newline(&trivia) {
        i.rollback(checkpoint);
        None
    } else {
        Some(trivia)
    }
}

fn enum_variant_exact_from_pending<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let word = i.run(scan_word)?;
    if word.text() == "from" {
        Some(word.range())
    } else {
        i.rollback(checkpoint);
        None
    }
}

fn enum_variant_payload_open<E>(delimiter: Delimiter, i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    if punctuation.kind() == PunctuationKind::Open(delimiter) {
        Some(punctuation.range())
    } else {
        i.rollback(checkpoint);
        None
    }
}

fn parse_variant_named_field_ast<'source, E>(
    spec: VariantFieldDriverSpec,
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
    } else if struct_colon_pending(i)
        || matches!(
            name_recovery,
            Some(StructFieldInvalidRun {
                target: StructFieldInvalidTarget::Colon { .. },
                ..
            })
        )
    {
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
    let colon = scan_struct_colon(i)
        .map(Recovered::Complete)
        .unwrap_or(Recovered::Incomplete);
    let type_expr = if (ambient_sensitive && any_ambient_owner_claims(i))
        || matches!(
            colon_recovery,
            Some(StructFieldInvalidRun {
                target: StructFieldInvalidTarget::Boundary,
                ..
            })
        )
        || (matches!(colon, Recovered::Incomplete) && struct_field_boundary_pending(i))
    {
        Recovered::Incomplete
    } else {
        let _ = consume_struct_field_type_trivia(i);
        let owner = spec.named_type_owner();
        i.local.push_type_delimited_owner(owner);
        let parsed = i
            .run(from_fn(|i| {
                Some(parse_required_type_expression_with_outer_missing_role(
                    Some(spec.type_role()),
                    i,
                ))
            }))
            .expect("mandatory shared named field TypeExpression is total");
        assert_eq!(i.local.pop_type_delimited_owner(), Some(owner));
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
    Some(StructNamedField {
        name,
        colon,
        type_expr,
        range: start..end,
    })
}

fn parse_variant_tuple_field_ast<'source, E>(
    spec: VariantFieldDriverSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<StructTupleField<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let owner = (spec != VariantFieldDriverSpec::Struct).then(|| spec.named_type_owner());
    if let Some(owner) = owner {
        i.local.push_type_delimited_owner(owner);
    }
    let parsed = match spec {
        VariantFieldDriverSpec::Struct => i
            .run(from_fn(|i| {
                Some(parse_required_type_expression_with_outer_missing_role(
                    Some(spec.type_role()),
                    i,
                ))
            }))
            .expect("mandatory Struct tuple field TypeExpression is total"),
        VariantFieldDriverSpec::EnumNamed
        | VariantFieldDriverSpec::EnumTuple
        | VariantFieldDriverSpec::ErrorNamed
        | VariantFieldDriverSpec::ErrorTuple => {
            match parse_required_variant_declaration_tuple_field_type_expression(spec, i) {
                Recovered::Complete(type_expr) => Recovered::Complete(*type_expr),
                Recovered::Incomplete => Recovered::Incomplete,
            }
        }
    };
    if let Some(owner) = owner {
        assert_eq!(i.local.pop_type_delimited_owner(), Some(owner));
    }
    match parsed {
        Recovered::Complete(type_expr) => {
            let range = type_expr.range();
            Recovered::Complete(StructTupleField {
                type_expr: Recovered::Complete(Box::new(type_expr)),
                range,
            })
        }
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

/// Parse a complete variant payload after its raw name.  This stays detached
/// from the declaration header and real statement dispatch; Gate 7 owns that
/// form-level composition.  The priority is intentionally syntactic and
/// left-to-right so `from`, `{`, and `(` never leak into positional parsing.
fn parse_variant_declaration_payload_ast<'source, E>(
    owner: VariantDeclarationOwnerSpec,
    form: VariantDeclarationSequenceForm,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> EnumVariantPayload<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    // Named and tuple payload delimiters are owned immediately after the raw
    // variant name. Their grammar has no required payload trivia, so `B(T)`
    // and `A { field: T }` must outrank both unit and positional evidence.
    if let Some(open) = enum_variant_payload_open(Delimiter::Brace, i) {
        return parse_variant_declaration_named_payload_ast(owner, form, open, i);
    }
    if let Some(open) = enum_variant_payload_open(Delimiter::Parenthesis, i) {
        return parse_variant_declaration_tuple_payload_ast(owner, form, open, i);
    }
    let Some(_) = consume_enum_variant_payload_trivia(i) else {
        return EnumVariantPayload::Unit;
    };
    if let Some(keyword) = enum_variant_exact_from_pending(i) {
        let _ = consume_enum_variant_payload_trivia(i);
        let type_expr = parse_required_variant_declaration_type_expression(
            owner,
            EnumVariantTypeExpressionSlot::FromType,
            form,
            i,
        );
        let end = match &type_expr {
            Recovered::Complete(type_expr) => type_expr.range().end,
            Recovered::Incomplete => keyword.end,
        };
        return EnumVariantPayload::From {
            keyword: keyword.clone(),
            type_expr,
            range: keyword.start..end,
        };
    }
    if let Some(open) = enum_variant_payload_open(Delimiter::Brace, i) {
        return parse_variant_declaration_named_payload_ast(owner, form, open, i);
    }
    if let Some(open) = enum_variant_payload_open(Delimiter::Parenthesis, i) {
        return parse_variant_declaration_tuple_payload_ast(owner, form, open, i);
    }
    if enum_variant_positional_payload_pending(form, i) {
        let first = parse_required_variant_declaration_type_expression(
            owner,
            EnumVariantTypeExpressionSlot::PositionalPayload,
            form,
            i,
        );
        let start = match &first {
            Recovered::Complete(type_expr) => type_expr.range().start,
            Recovered::Incomplete => i.pos(),
        };
        let mut types = vec![first];
        loop {
            let position = i.checkpoint();
            if consume_enum_variant_payload_trivia(i).is_none()
                || !enum_variant_positional_payload_pending(form, i)
            {
                i.rollback(position);
                break;
            }
            types.push(parse_required_variant_declaration_type_expression(
                owner,
                EnumVariantTypeExpressionSlot::PositionalPayload,
                form,
                i,
            ));
        }
        let end = types
            .iter()
            .rev()
            .find_map(|item| match item {
                Recovered::Complete(type_expr) => Some(type_expr.range().end),
                Recovered::Incomplete => None,
            })
            .unwrap_or(start);
        return EnumVariantPayload::Positional {
            types,
            range: start..end,
        };
    }
    i.rollback(checkpoint);
    EnumVariantPayload::Unit
}

fn parse_variant_declaration_named_payload_ast<'source, E>(
    owner: VariantDeclarationOwnerSpec,
    _form: VariantDeclarationSequenceForm,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> EnumVariantPayload<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
        .without(StopKind::Newline)
        .with(StopKind::Comma)
        .with(StopKind::RightBrace);
    i.local.push_delimiter(Delimiter::Brace);
    i.local.push_stop_set(stops);
    let opening = i.run(scan_trivia).expect("trivia is total");
    let layout =
        LayoutDelimitedFrame::after_opening_trivia(0, &opening, i.local.line().line_indent);
    push_struct_layout(layout, i);
    let mut fields = Vec::new();
    let mut trailing_comma = None;
    let close = loop {
        if let Some(close) = scan_struct_close_brace(i) {
            break Recovered::Complete(close);
        }
        if i.input.remainder().is_empty() || struct_outer_owned_mismatched_close_pending(i) {
            break Recovered::Incomplete;
        }
        if scan_struct_comma(i).is_some() {
            fields.push(Recovered::Incomplete);
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        let field = parse_variant_named_field_ast(owner.field_driver, true, i)
            .map(Recovered::Complete)
            .unwrap_or(Recovered::Incomplete);
        let incomplete = matches!(field, Recovered::Incomplete);
        fields.push(field);
        if incomplete || any_ambient_owner_claims(i) {
            break Recovered::Incomplete;
        }
        let trivia = i.run(scan_trivia).expect("trivia is total");
        if let Some(comma) = scan_struct_comma(i) {
            let _ = i.run(scan_trivia).expect("trivia is total");
            if let Some(close) = scan_struct_close_brace(i) {
                trailing_comma = Some(comma);
                break Recovered::Complete(close);
            }
            continue;
        }
        if let Some(close) = scan_struct_close_brace(i) {
            break Recovered::Complete(close);
        }
        if layout.boundary_after_trivia(&trivia, i.local.line().line_indent)
            == LayoutDelimitedBoundary::ImplicitNewline
        {
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
    EnumVariantPayload::Named {
        open: open.clone(),
        fields,
        trailing_comma,
        close,
        range: open.start..end,
    }
}

fn parse_variant_declaration_tuple_payload_ast<'source, E>(
    owner: VariantDeclarationOwnerSpec,
    _form: VariantDeclarationSequenceForm,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> EnumVariantPayload<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
        .without(StopKind::Newline)
        .with(StopKind::Comma)
        .with(StopKind::RightParenthesis);
    i.local.push_delimiter(Delimiter::Parenthesis);
    i.local.push_stop_set(stops);
    let _ = i.run(scan_trivia).expect("trivia is total");
    let mut fields = Vec::new();
    let mut trailing_comma = None;
    let close = loop {
        if let Some(close) = scan_struct_close_parenthesis(i) {
            break Recovered::Complete(close);
        }
        if i.input.remainder().is_empty()
            || struct_outer_owned_mismatched_close_pending_for(Delimiter::Parenthesis, i)
        {
            break Recovered::Incomplete;
        }
        if scan_struct_comma(i).is_some() {
            fields.push(Recovered::Incomplete);
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        let field = parse_variant_tuple_field_ast(owner.field_driver.tuple_payload(), i);
        let incomplete = matches!(field, Recovered::Incomplete);
        fields.push(field);
        if incomplete || any_ambient_owner_claims(i) {
            break Recovered::Incomplete;
        }
        let trivia = i.run(scan_trivia).expect("trivia is total");
        if let Some(comma) = scan_struct_comma(i) {
            let _ = i.run(scan_trivia).expect("trivia is total");
            if let Some(close) = scan_struct_close_parenthesis(i) {
                trailing_comma = Some(comma);
                break Recovered::Complete(close);
            }
            continue;
        }
        if let Some(close) = scan_struct_close_parenthesis(i) {
            break Recovered::Complete(close);
        }
        if LayoutDelimitedFrame::inline(0)
            .boundary_after_trivia(&trivia, i.local.line().line_indent)
            == LayoutDelimitedBoundary::ImplicitNewline
        {
            continue;
        }
        break Recovered::Incomplete;
    };
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    let end = match &close {
        Recovered::Complete(close) => close.end,
        Recovered::Incomplete => i.pos(),
    };
    EnumVariantPayload::Tuple {
        open: open.clone(),
        fields,
        trailing_comma,
        close,
        range: open.start..end,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedEnumVariantSequence<'source> {
    variants: Vec<Recovered<EnumVariant<'source>>>,
    trailing_comma: Option<Range<usize>>,
    trailing_pipe: Option<Range<usize>>,
    close: Recovered<Range<usize>>,
    termination: EnumVariantSequenceTermination,
}

struct AstEnumVariantPayloadContext<'context, 'parse, 'source, 'local, E: ErrorSink<usize>> {
    i: &'context mut SynIn<'parse, 'source, 'local, E>,
    spec: VariantDeclarationSequenceSpec,
    owner: VariantDeclarationOwnerSpec,
    variants: Vec<Recovered<EnumVariant<'source>>>,
    trailing_comma: Option<Range<usize>>,
    trailing_pipe: Option<Range<usize>>,
    close: Recovered<Range<usize>>,
}

impl<'source, E> VariantDeclarationSequenceContext<'source>
    for AstEnumVariantPayloadContext<'_, '_, 'source, '_, E>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    type Error = E;

    fn with_input<R>(&mut self, f: impl FnOnce(&mut SynIn<'_, 'source, '_, E>) -> R) -> R {
        f(self.i)
    }

    fn emit_trivia(&mut self, _trivia: &TriviaRun) {}

    fn emit_missing_variant(&mut self) {
        self.variants.push(Recovered::Incomplete);
    }

    fn emit_separator(&mut self, _separator: EnumVariantSeparator) {}

    fn set_trailing_separator(&mut self, separator: EnumVariantSeparator) {
        match separator {
            EnumVariantSeparator::Comma(range) => self.trailing_comma = Some(range),
            EnumVariantSeparator::Pipe(range) => self.trailing_pipe = Some(range),
        }
    }

    fn emit_matching_close(&mut self, close: Range<usize>) {
        self.close = Recovered::Complete(close);
    }

    fn parse_variant_item(&mut self, malformed: Option<Range<usize>>) -> bool {
        let start = malformed
            .as_ref()
            .map_or_else(|| self.i.pos(), |range| range.start);
        if let Some(range) = malformed {
            while self.i.pos() < range.end {
                self.i
                    .input
                    .next()
                    .expect("the selected Enum variant error range remains available");
                let mut line = self.i.local.line();
                line.at_line_start = false;
                self.i.local.set_line(line);
            }
        }
        let Some(name) = self.i.run(scan_word) else {
            self.variants.push(Recovered::Incomplete);
            return true;
        };
        let payload = parse_variant_declaration_payload_ast(self.owner, self.spec.form, self.i);
        let end = match &payload {
            EnumVariantPayload::Unit => name.range().end,
            EnumVariantPayload::From { range, .. }
            | EnumVariantPayload::Named { range, .. }
            | EnumVariantPayload::Tuple { range, .. }
            | EnumVariantPayload::Positional { range, .. } => range.end,
        };
        self.variants.push(Recovered::Complete(EnumVariant {
            name: Recovered::Complete(name),
            payload,
            range: start..end,
        }));
        true
    }
}

/// The Gate 6 payload adapter replaces Gate 5's raw-word stub without taking
/// ownership of an Enum header or body-form starter.  Later form adapters
/// supply the frame and consume the returned close/boundary fact.
fn parse_variant_declaration_sequence_with_payload<'source, E>(
    spec: VariantDeclarationSequenceSpec,
    owner: VariantDeclarationOwnerSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ParsedEnumVariantSequence<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut context = AstEnumVariantPayloadContext {
        i,
        spec,
        owner,
        variants: Vec::new(),
        trailing_comma: None,
        trailing_pipe: None,
        close: Recovered::Incomplete,
    };
    debug_assert_eq!(spec.declaration_base, owner.declaration_base);
    let termination = drive_variant_declaration_sequence(&mut context, spec);
    ParsedEnumVariantSequence {
        variants: context.variants,
        trailing_comma: context.trailing_comma,
        trailing_pipe: context.trailing_pipe,
        close: context.close,
        termination,
    }
}

/// Retains the Enum-only fixture entry point while production body adapters
/// pass their owner spec explicitly to the neutral core.
fn parse_enum_variant_sequence_with_payload<'source, E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ParsedEnumVariantSequence<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_variant_declaration_sequence_with_payload(
        spec,
        enum_variant_declaration_owner_spec(spec.declaration_base),
        i,
    )
}

fn emit_variant_declaration_missing<'parse, 'source, 'local, E, O>(
    role: GrammarRole,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
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
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_enum_variant_item_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.start_node(SyntaxKind::EnumVariant);
    emit_variant_declaration_missing(
        enum_variant_declaration_owner_spec(0).item_role,
        committed,
        ExpectedSyntax::Identifier,
    );
    committed.finish_node();
}

fn emit_error_variant_item_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.start_node(SyntaxKind::EnumVariant);
    emit_variant_declaration_missing(
        error_variant_declaration_owner_spec(0).item_role,
        committed,
        ExpectedSyntax::Identifier,
    );
    committed.finish_node();
}

fn emit_enum_declaration_error<'parse, 'source, 'local, E, O>(
    enum_role: EnumDeclarationRole,
    range: Range<usize>,
    expected: ExpectedSyntax,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Enum(enum_role));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
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

fn emit_error_declaration_error<'parse, 'source, 'local, E, O>(
    error_role: ErrorDeclarationRole,
    range: Range<usize>,
    expected: ExpectedSyntax,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Error(error_role));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
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

fn emit_enum_braced_close_error<'parse, 'source, 'local, E, O>(
    range: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::ClosingDelimiter {
            owner: ConstructRole::EnumBracedVariantBody,
            delimiter: Delimiter::Brace,
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    Delimiter::Brace,
                )),
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn emit_enum_braced_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::ClosingDelimiter {
            owner: ConstructRole::EnumBracedVariantBody,
            delimiter: Delimiter::Brace,
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
                    Delimiter::Brace,
                )),
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn consume_source_range<E>(range: Range<usize>, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    debug_assert_eq!(i.pos(), range.start);
    while i.pos() < range.end {
        i.input
            .next()
            .expect("the selected recovery range remains available");
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
    debug_assert_eq!(i.pos(), range.end);
}

fn emit_variant_declaration_error<'parse, 'source, 'local, E, O>(
    role: GrammarRole,
    range: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
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

fn emit_variant_payload_missing_close<'parse, 'source, 'local, E, O>(
    owner: ConstructRole,
    delimiter: Delimiter,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::ClosingDelimiter { owner, delimiter };
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

fn commit_variant_tuple_field<'parse, 'source, 'local, E, O>(
    spec: VariantFieldDriverSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::StructField);
    let owner = (spec != VariantFieldDriverSpec::Struct).then(|| spec.named_type_owner());
    if let Some(owner) = owner {
        committed.probe(|probe| {
            probe.input().local.push_type_delimited_owner(owner);
        });
    }
    match spec {
        VariantFieldDriverSpec::Struct => {
            let _ = commit_direct_type_expression_with_outer_missing_role(
                Some(spec.type_role()),
                committed,
            );
        }
        VariantFieldDriverSpec::EnumNamed
        | VariantFieldDriverSpec::EnumTuple
        | VariantFieldDriverSpec::ErrorNamed
        | VariantFieldDriverSpec::ErrorTuple => {
            let _ =
                commit_required_variant_declaration_tuple_field_type_expression(spec, committed);
        }
    }
    if let Some(owner) = owner {
        committed.probe(|probe| {
            assert_eq!(probe.input().local.pop_type_delimited_owner(), Some(owner));
        });
    }
    committed.finish_node();
}

fn commit_variant_declaration_named_payload<'parse, 'source, 'local, E, O>(
    owner: VariantDeclarationOwnerSpec,
    _form: VariantDeclarationSequenceForm,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.token(SyntaxKind::LBrace, open);
    let stops = committed.probe(|probe| {
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
            .without(StopKind::Newline)
            .with(StopKind::Comma)
            .with(StopKind::RightBrace)
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_delimiter(Delimiter::Brace);
        i.local.push_stop_set(stops);
    });
    let opening = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia is total");
    committed.emit_trivia(&opening);
    let layout = committed.probe(|probe| {
        LayoutDelimitedFrame::after_opening_trivia(
            0,
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
        if committed.probe(|probe| {
            probe.input().input.remainder().is_empty()
                || struct_outer_owned_mismatched_close_pending(probe.input())
        }) {
            emit_variant_payload_missing_close(
                ConstructRole::VariantNamedPayload,
                Delimiter::Brace,
                committed,
            );
            break;
        }
        if let Some(comma) = committed.probe(|probe| scan_struct_comma(probe.input())) {
            committed.start_node(SyntaxKind::StructField);
            emit_variant_field_missing(
                owner.field_driver,
                VariantFieldRecoverySlot::Item,
                committed,
                ExpectedSyntax::Identifier,
            );
            committed.finish_node();
            committed.token(SyntaxKind::Comma, comma);
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if !commit_variant_named_field(owner.field_driver, true, committed) {
            if let Some(run) =
                committed.probe(|probe| scan_struct_field_invalid_run(false, probe.input()))
            {
                committed.start_node(SyntaxKind::StructField);
                emit_variant_field_error(
                    owner.field_driver,
                    VariantFieldRecoverySlot::Item,
                    committed,
                    run.range.clone(),
                    ExpectedSyntax::Identifier,
                );
                committed.probe(|probe| consume_source_range(run.range, probe.input()));
                committed.finish_node();
            } else {
                committed.start_node(SyntaxKind::StructField);
                emit_variant_field_missing(
                    owner.field_driver,
                    VariantFieldRecoverySlot::Item,
                    committed,
                    ExpectedSyntax::Identifier,
                );
                committed.finish_node();
                emit_variant_payload_missing_close(
                    ConstructRole::VariantNamedPayload,
                    Delimiter::Brace,
                    committed,
                );
                break;
            }
        }
        let trivia = committed
            .probe(|probe| probe.input().run(scan_trivia))
            .expect("trivia is total");
        committed.emit_trivia(&trivia);
        if let Some(comma) = committed.probe(|probe| scan_struct_comma(probe.input())) {
            committed.token(SyntaxKind::Comma, comma);
            let post = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&post);
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
            continue;
        }
        emit_variant_payload_missing_close(
            ConstructRole::VariantNamedPayload,
            Delimiter::Brace,
            committed,
        );
        break;
    }
    committed.probe(|probe| {
        let i = probe.input();
        pop_struct_layout(layout, i);
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Brace));
    });
}

fn commit_variant_declaration_tuple_payload<'parse, 'source, 'local, E, O>(
    owner: VariantDeclarationOwnerSpec,
    _form: VariantDeclarationSequenceForm,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.token(SyntaxKind::LParen, open);
    let stops = committed.probe(|probe| {
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
            .without(StopKind::Newline)
            .with(StopKind::Comma)
            .with(StopKind::RightParenthesis)
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_delimiter(Delimiter::Parenthesis);
        i.local.push_stop_set(stops);
    });
    let opening = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia is total");
    committed.emit_trivia(&opening);
    loop {
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
            emit_variant_payload_missing_close(
                ConstructRole::VariantTuplePayload,
                Delimiter::Parenthesis,
                committed,
            );
            break;
        }
        if committed.probe(|probe| scan_struct_comma_pending(probe.input())) {
            commit_variant_tuple_field(owner.field_driver.tuple_payload(), committed);
            let comma = committed
                .probe(|probe| scan_struct_comma(probe.input()))
                .expect("the empty Enum tuple field slot is followed by its comma");
            committed.token(SyntaxKind::Comma, comma);
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        commit_variant_tuple_field(owner.field_driver.tuple_payload(), committed);
        let trivia = committed
            .probe(|probe| probe.input().run(scan_trivia))
            .expect("trivia is total");
        committed.emit_trivia(&trivia);
        if let Some(comma) = committed.probe(|probe| scan_struct_comma(probe.input())) {
            committed.token(SyntaxKind::Comma, comma);
            let post = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&post);
            continue;
        }
        if let Some(close) = committed.probe(|probe| scan_struct_close_parenthesis(probe.input())) {
            committed.token(SyntaxKind::RParen, close);
            break;
        }
        emit_variant_payload_missing_close(
            ConstructRole::VariantTuplePayload,
            Delimiter::Parenthesis,
            committed,
        );
        break;
    }
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    });
}

fn commit_variant_declaration_payload<'parse, 'source, 'local, E, O>(
    owner: VariantDeclarationOwnerSpec,
    form: VariantDeclarationSequenceForm,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    if let Some(open) =
        committed.probe(|probe| enum_variant_payload_open(Delimiter::Brace, probe.input()))
    {
        commit_variant_declaration_named_payload(owner, form, open, committed);
        return;
    }
    if let Some(open) =
        committed.probe(|probe| enum_variant_payload_open(Delimiter::Parenthesis, probe.input()))
    {
        commit_variant_declaration_tuple_payload(owner, form, open, committed);
        return;
    }
    let gap = committed.probe(|probe| consume_enum_variant_payload_trivia(probe.input()));
    let Some(gap) = gap else {
        return;
    };
    if let Some(keyword) = committed.probe(|probe| enum_variant_exact_from_pending(probe.input())) {
        committed.emit_trivia(&gap);
        committed.token(SyntaxKind::FromKw, keyword);
        if let Some(trivia) =
            committed.probe(|probe| consume_enum_variant_payload_trivia(probe.input()))
        {
            committed.emit_trivia(&trivia);
        }
        let _ = commit_required_variant_declaration_type_expression(
            owner,
            EnumVariantTypeExpressionSlot::FromType,
            form,
            committed,
        );
        return;
    }
    if let Some(open) =
        committed.probe(|probe| enum_variant_payload_open(Delimiter::Brace, probe.input()))
    {
        committed.emit_trivia(&gap);
        commit_variant_declaration_named_payload(owner, form, open, committed);
        return;
    }
    if let Some(open) =
        committed.probe(|probe| enum_variant_payload_open(Delimiter::Parenthesis, probe.input()))
    {
        committed.emit_trivia(&gap);
        commit_variant_declaration_tuple_payload(owner, form, open, committed);
        return;
    }
    if committed.probe(|probe| enum_variant_positional_payload_pending(form, probe.input())) {
        committed.emit_trivia(&gap);
        let _ = commit_required_variant_declaration_type_expression(
            owner,
            EnumVariantTypeExpressionSlot::PositionalPayload,
            form,
            committed,
        );
        loop {
            let checkpoint = committed.probe(|probe| probe.input().checkpoint());
            let Some(trivia) =
                committed.probe(|probe| consume_enum_variant_payload_trivia(probe.input()))
            else {
                break;
            };
            if !committed
                .probe(|probe| enum_variant_positional_payload_pending(form, probe.input()))
            {
                committed.probe(|probe| probe.input().rollback(checkpoint));
                break;
            }
            committed.emit_trivia(&trivia);
            let _ = commit_required_variant_declaration_type_expression(
                owner,
                EnumVariantTypeExpressionSlot::PositionalPayload,
                form,
                committed,
            );
        }
        return;
    }
    committed.probe(|probe| probe.input().rollback(checkpoint));
}

struct DirectEnumVariantPayloadContext<
    'context,
    'parse,
    'source,
    'local,
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
> {
    committed: &'context mut Committed<'parse, 'source, 'local, E, O>,
    spec: VariantDeclarationSequenceSpec,
    owner: VariantDeclarationOwnerSpec,
}

impl<'source, E, O> VariantDeclarationSequenceContext<'source>
    for DirectEnumVariantPayloadContext<'_, '_, 'source, '_, E, O>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    type Error = E;

    fn with_input<R>(&mut self, f: impl FnOnce(&mut SynIn<'_, 'source, '_, E>) -> R) -> R {
        self.committed.probe(|probe| f(probe.input()))
    }

    fn emit_trivia(&mut self, trivia: &TriviaRun) {
        self.committed.emit_trivia(trivia);
    }

    fn emit_missing_variant(&mut self) {
        self.committed.start_node(SyntaxKind::EnumVariant);
        emit_variant_declaration_missing(
            self.owner.item_role,
            self.committed,
            ExpectedSyntax::Identifier,
        );
        self.committed.finish_node();
    }

    fn emit_separator(&mut self, separator: EnumVariantSeparator) {
        match separator {
            EnumVariantSeparator::Comma(range) => self.committed.token(SyntaxKind::Comma, range),
            EnumVariantSeparator::Pipe(range) => self.committed.token(SyntaxKind::Pipe, range),
        }
    }

    fn set_trailing_separator(&mut self, _separator: EnumVariantSeparator) {}

    fn emit_matching_close(&mut self, close: Range<usize>) {
        self.committed.token(SyntaxKind::RBrace, close);
    }

    fn parse_variant_item(&mut self, malformed: Option<Range<usize>>) -> bool {
        self.committed.start_node(SyntaxKind::EnumVariant);
        if let Some(range) = malformed {
            let has_raw_name_retry = self
                .committed
                .probe(|probe| enum_variant_raw_name_pending(probe.input()));
            emit_variant_declaration_error(
                if has_raw_name_retry {
                    self.owner.variant_role(VariantDeclarationRole::Name)
                } else {
                    self.owner.item_role
                },
                range.clone(),
                self.committed,
                ExpectedSyntax::Identifier,
            );
            if !has_raw_name_retry {
                self.committed.finish_node();
                return true;
            }
        }
        let Some(name) = self.committed.probe(|probe| probe.input().run(scan_word)) else {
            emit_variant_declaration_missing(
                self.owner.variant_role(VariantDeclarationRole::Name),
                self.committed,
                ExpectedSyntax::Identifier,
            );
            self.committed.finish_node();
            return true;
        };
        self.committed.token(SyntaxKind::Identifier, name.range());
        commit_variant_declaration_payload(self.owner, self.spec.form, self.committed);
        self.committed.finish_node();
        true
    }
}

fn commit_variant_declaration_sequence_with_payload<'parse, 'source, 'local, E, O>(
    spec: VariantDeclarationSequenceSpec,
    owner: VariantDeclarationOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> EnumVariantSequenceTermination
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    debug_assert_eq!(spec.declaration_base, owner.declaration_base);
    let mut context = DirectEnumVariantPayloadContext {
        committed,
        spec,
        owner,
    };
    drive_variant_declaration_sequence(&mut context, spec)
}

/// Retains Enum's fixture entry point while its declaration adapters call
/// the neutral core with their owner spec explicitly.
fn commit_enum_variant_sequence_with_payload<'parse, 'source, 'local, E, O>(
    spec: EnumVariantSequenceSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> EnumVariantSequenceTermination
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_variant_declaration_sequence_with_payload(
        spec,
        enum_variant_declaration_owner_spec(spec.declaration_base),
        committed,
    )
}

/// Parses one accepted Enum continuation shared by isolated fixtures and
/// Gate 11's promoted public statement dispatch. Header derives, body-form
/// selection, and the variant sequence remain on this one path.
#[allow(dead_code)]
pub(crate) fn parse_enum_declaration_isolated<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<EnumDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let declaration = (|| {
        let intro = i.run(recognize_enum_statement_intro)?;
        let (header, _recoveries) = parse_required_enum_header_isolated(&intro, &mut i);
        let header_complete = matches!(header.name, Recovered::Complete(_));
        let mut derives = header_complete
            .then(|| {
                recognize_derives_attachment_start(
                    DerivesAttachmentOwner::Enum,
                    DerivesAttachmentPosition::Header,
                    intro.enum_base,
                    &mut i,
                )
                .map(|start| parse_derives_attachments_isolated(start, &mut i))
                .unwrap_or_default()
            })
            .unwrap_or_default();
        let body = header_complete
            .then(|| parse_enum_body_ast(intro.enum_base, &mut i))
            .unwrap_or(Recovered::Incomplete);
        if enum_body_has_actual_trailing_close(&body) {
            if let Some(start) = recognize_derives_attachment_start(
                DerivesAttachmentOwner::Enum,
                DerivesAttachmentPosition::Trailing,
                intro.enum_base,
                &mut i,
            ) {
                derives.extend(parse_derives_attachments_isolated(start, &mut i));
            }
        }
        let header_end = match &header.name {
            Recovered::Complete(name) => header
                .parameters
                .last()
                .map_or_else(|| name.range().end, declaration_type_parameter_end),
            Recovered::Incomplete => intro.enum_keyword.range().end,
        };
        let body_end = enum_body_range_end(&body).unwrap_or(header_end);
        let derives_end = derives
            .last()
            .map_or(0, |attachment| attachment.clause.range.end);
        Some(EnumDeclaration {
            visibility: intro
                .visibility
                .map_or(Visibility::Private, |prefix| prefix.visibility),
            name: header.name,
            parameters: header.parameters,
            derives,
            body,
            range: intro.start..header_end.max(body_end).max(derives_end),
        })
    })();
    i.errors_rollback(errors_checkpoint);
    declaration
}

/// Parses one accepted Error continuation shared by isolated fixtures and
/// Gate 9's promoted public statement dispatch. Its declaration identity
/// remains Error-specific; only the established Enum body vocabulary is shared.
pub(crate) fn parse_error_declaration_isolated<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ErrorDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let declaration = (|| {
        let intro = i.run(recognize_error_statement_intro)?;
        let (header, _recoveries) = parse_required_error_header_isolated(&intro, &mut i);
        let header_complete = matches!(header.name, Recovered::Complete(_));
        let mut derives = header_complete
            .then(|| {
                recognize_derives_attachment_start(
                    DerivesAttachmentOwner::Error,
                    DerivesAttachmentPosition::Header,
                    intro.error_base,
                    &mut i,
                )
                .map(|start| parse_derives_attachments_isolated(start, &mut i))
                .unwrap_or_default()
            })
            .unwrap_or_default();
        let body = header_complete
            .then(|| parse_error_body_ast(intro.error_base, &mut i))
            .unwrap_or(Recovered::Incomplete);
        if enum_body_has_actual_trailing_close(&body) {
            if let Some(start) = recognize_derives_attachment_start(
                DerivesAttachmentOwner::Error,
                DerivesAttachmentPosition::Trailing,
                intro.error_base,
                &mut i,
            ) {
                derives.extend(parse_derives_attachments_isolated(start, &mut i));
            }
        }
        let header_end = match &header.name {
            Recovered::Complete(name) => header
                .parameters
                .last()
                .map_or_else(|| name.range().end, declaration_type_parameter_end),
            Recovered::Incomplete => intro.error_keyword.range().end,
        };
        let body_end = enum_body_range_end(&body).unwrap_or(header_end);
        let derives_end = derives
            .last()
            .map_or(0, |attachment| attachment.clause.range.end);
        Some(ErrorDeclaration {
            visibility: intro
                .visibility
                .map_or(Visibility::Private, |prefix| prefix.visibility),
            name: header.name,
            parameters: header.parameters,
            derives,
            body,
            range: intro.start..header_end.max(body_end).max(derives_end),
        })
    })();
    i.errors_rollback(errors_checkpoint);
    declaration
}

fn declaration_type_parameter_end(parameter: &DeclarationTypeParameter<'_>) -> usize {
    declaration_type_parameter_range(parameter).end
}

fn enum_body_range_end(body: &Recovered<EnumBody<'_>>) -> Option<usize> {
    match body {
        Recovered::Incomplete => None,
        Recovered::Complete(EnumBody::Bodyless {
            semicolon: Some(semicolon),
        }) => Some(semicolon.end),
        Recovered::Complete(EnumBody::Bodyless { semicolon: None }) => None,
        Recovered::Complete(EnumBody::Braced(body)) => Some(body.range.end),
        Recovered::Complete(EnumBody::Colon { colon, body }) => match body {
            Recovered::Complete(body) => Some(body.range.end),
            Recovered::Incomplete => Some(colon.end),
        },
        Recovered::Complete(EnumBody::Equals { equals, body }) => match body {
            Recovered::Complete(EnumEqualsVariantBody::Inline { range, .. }) => Some(range.end),
            Recovered::Complete(EnumEqualsVariantBody::Indented(body)) => Some(body.range.end),
            Recovered::Incomplete => Some(equals.end),
        },
    }
}

fn variant_declaration_sequence_spec(
    form: VariantDeclarationSequenceForm,
    layout: LayoutDelimitedFrame,
    declaration_base: usize,
) -> VariantDeclarationSequenceSpec {
    match form {
        VariantDeclarationSequenceForm::Braced => VariantDeclarationSequenceSpec {
            form,
            layout,
            declaration_base,
            explicit_separators: EnumVariantSeparatorSet::new(true, false),
            matching_close: Some(Delimiter::Brace),
            allow_leading_pipe: false,
            allow_trailing_pipe: false,
        },
        VariantDeclarationSequenceForm::ColonIndented
        | VariantDeclarationSequenceForm::EqualsIndented => VariantDeclarationSequenceSpec {
            form,
            layout,
            declaration_base,
            explicit_separators: EnumVariantSeparatorSet::new(true, true),
            matching_close: None,
            allow_leading_pipe: true,
            allow_trailing_pipe: true,
        },
        VariantDeclarationSequenceForm::EqualsInline => VariantDeclarationSequenceSpec {
            form,
            layout,
            declaration_base,
            explicit_separators: EnumVariantSeparatorSet::new(false, true),
            matching_close: None,
            allow_leading_pipe: true,
            allow_trailing_pipe: true,
        },
    }
}

fn parse_enum_body_ast<'source, E>(
    enum_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<EnumBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if enum_body_implicit_boundary_pending(enum_base, i) {
        return Recovered::Complete(EnumBody::Bodyless { semicolon: None });
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(enum_base, i) else {
        i.rollback(checkpoint);
        return Recovered::Complete(EnumBody::Bodyless { semicolon: None });
    };

    if let Some(equals) = i.run(scan_declaration_exact_equals) {
        return Recovered::Complete(EnumBody::Equals {
            equals: equals.clone(),
            body: parse_enum_equals_body_ast(enum_base, equals, i),
        });
    }
    let punctuation_checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation);
    match punctuation.map(|punctuation| (punctuation.kind(), punctuation.range())) {
        Some((PunctuationKind::Semicolon, semicolon)) => Recovered::Complete(EnumBody::Bodyless {
            semicolon: Some(semicolon),
        }),
        Some((PunctuationKind::Open(Delimiter::Brace), open)) => Recovered::Complete(
            EnumBody::Braced(parse_enum_braced_body_ast(enum_base, open, i)),
        ),
        Some((PunctuationKind::Colon, colon)) => Recovered::Complete(EnumBody::Colon {
            colon: colon.clone(),
            body: parse_enum_colon_body_ast(enum_base, colon, i),
        }),
        _ => {
            i.rollback(punctuation_checkpoint);
            i.rollback(checkpoint);
            match enum_body_introducer_error_retry_ast(enum_base, i) {
                Some(true) => parse_enum_body_ast(enum_base, i),
                Some(false) | None => Recovered::Incomplete,
            }
        }
    }
}

fn parse_enum_braced_body_ast<'source, E>(
    enum_base: usize,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> EnumBracedBody<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let opening = i.run(scan_trivia).expect("trivia scanning is total");
    let layout =
        LayoutDelimitedFrame::after_opening_trivia(enum_base, &opening, i.local.line().line_indent);
    let sequence = parse_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::Braced,
            layout,
            enum_base,
        ),
        enum_variant_declaration_owner_spec(enum_base),
        i,
    );
    let end = match &sequence.close {
        Recovered::Complete(close) => close.end,
        Recovered::Incomplete => i.pos(),
    };
    EnumBracedBody {
        open: open.clone(),
        variants: sequence.variants,
        trailing_comma: sequence.trailing_comma,
        close: sequence.close,
        range: open.start..end,
    }
}

fn parse_enum_colon_body_ast<'source, E>(
    enum_base: usize,
    colon: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<EnumIndentedVariantBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    if !enum_variant_trivia_has_newline(&trivia) || i.local.line().line_indent <= enum_base {
        i.rollback(checkpoint);
        return Recovered::Incomplete;
    }
    let block_indent = i.local.line().line_indent;
    let sequence = parse_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::ColonIndented,
            LayoutDelimitedFrame::inline(block_indent),
            enum_base,
        ),
        enum_variant_declaration_owner_spec(enum_base),
        i,
    );
    let end = i.pos();
    let _ = sequence.trailing_pipe;
    Recovered::Complete(EnumIndentedVariantBody {
        base_indent: enum_base,
        block_indent,
        variants: sequence.variants,
        range: colon.end..end,
    })
}

fn parse_enum_equals_body_ast<'source, E>(
    enum_base: usize,
    equals: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<EnumEqualsVariantBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    if enum_variant_trivia_has_newline(&trivia) {
        if i.local.line().line_indent <= enum_base {
            i.rollback(checkpoint);
            return Recovered::Incomplete;
        }
        let block_indent = i.local.line().line_indent;
        let sequence = parse_variant_declaration_sequence_with_payload(
            variant_declaration_sequence_spec(
                VariantDeclarationSequenceForm::EqualsIndented,
                LayoutDelimitedFrame::inline(block_indent),
                enum_base,
            ),
            enum_variant_declaration_owner_spec(enum_base),
            i,
        );
        let end = i.pos();
        let _ = sequence.trailing_pipe;
        return Recovered::Complete(EnumEqualsVariantBody::Indented(EnumIndentedVariantBody {
            base_indent: enum_base,
            block_indent,
            variants: sequence.variants,
            range: equals.end..end,
        }));
    }
    let sequence = parse_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::EqualsInline,
            LayoutDelimitedFrame::inline(enum_base),
            enum_base,
        ),
        enum_variant_declaration_owner_spec(enum_base),
        i,
    );
    let end = i.pos();
    Recovered::Complete(EnumEqualsVariantBody::Inline {
        variants: sequence.variants,
        trailing_pipe: sequence.trailing_pipe,
        range: equals.end..end,
    })
}

fn parse_error_body_ast<'source, E>(
    error_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<EnumBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if enum_body_implicit_boundary_pending(error_base, i) {
        return Recovered::Complete(EnumBody::Bodyless { semicolon: None });
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(error_base, i) else {
        i.rollback(checkpoint);
        return Recovered::Complete(EnumBody::Bodyless { semicolon: None });
    };
    if let Some(equals) = i.run(scan_declaration_exact_equals) {
        return Recovered::Complete(EnumBody::Equals {
            equals: equals.clone(),
            body: parse_error_equals_body_ast(error_base, equals, i),
        });
    }
    let punctuation_checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation);
    match punctuation.map(|punctuation| (punctuation.kind(), punctuation.range())) {
        Some((PunctuationKind::Semicolon, semicolon)) => Recovered::Complete(EnumBody::Bodyless {
            semicolon: Some(semicolon),
        }),
        Some((PunctuationKind::Open(Delimiter::Brace), open)) => Recovered::Complete(
            EnumBody::Braced(parse_error_braced_body_ast(error_base, open, i)),
        ),
        Some((PunctuationKind::Colon, colon)) => Recovered::Complete(EnumBody::Colon {
            colon: colon.clone(),
            body: parse_error_colon_body_ast(error_base, colon, i),
        }),
        _ => {
            i.rollback(punctuation_checkpoint);
            i.rollback(checkpoint);
            match enum_body_introducer_error_retry_ast(error_base, i) {
                Some(true) => parse_error_body_ast(error_base, i),
                Some(false) | None => Recovered::Incomplete,
            }
        }
    }
}

fn parse_error_braced_body_ast<'source, E>(
    error_base: usize,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> EnumBracedBody<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let opening = i.run(scan_trivia).expect("trivia scanning is total");
    let layout = LayoutDelimitedFrame::after_opening_trivia(
        error_base,
        &opening,
        i.local.line().line_indent,
    );
    let sequence = parse_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::Braced,
            layout,
            error_base,
        ),
        error_variant_declaration_owner_spec(error_base),
        i,
    );
    let end = match &sequence.close {
        Recovered::Complete(close) => close.end,
        Recovered::Incomplete => i.pos(),
    };
    EnumBracedBody {
        open: open.clone(),
        variants: sequence.variants,
        trailing_comma: sequence.trailing_comma,
        close: sequence.close,
        range: open.start..end,
    }
}

fn parse_error_colon_body_ast<'source, E>(
    error_base: usize,
    colon: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<EnumIndentedVariantBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    if !enum_variant_trivia_has_newline(&trivia) || i.local.line().line_indent <= error_base {
        i.rollback(checkpoint);
        return Recovered::Incomplete;
    }
    let block_indent = i.local.line().line_indent;
    let sequence = parse_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::ColonIndented,
            LayoutDelimitedFrame::inline(block_indent),
            error_base,
        ),
        error_variant_declaration_owner_spec(error_base),
        i,
    );
    let end = i.pos();
    let _ = sequence.trailing_pipe;
    Recovered::Complete(EnumIndentedVariantBody {
        base_indent: error_base,
        block_indent,
        variants: sequence.variants,
        range: colon.end..end,
    })
}

fn parse_error_equals_body_ast<'source, E>(
    error_base: usize,
    equals: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<EnumEqualsVariantBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    if enum_variant_trivia_has_newline(&trivia) {
        if i.local.line().line_indent <= error_base {
            i.rollback(checkpoint);
            return Recovered::Incomplete;
        }
        let block_indent = i.local.line().line_indent;
        let sequence = parse_variant_declaration_sequence_with_payload(
            variant_declaration_sequence_spec(
                VariantDeclarationSequenceForm::EqualsIndented,
                LayoutDelimitedFrame::inline(block_indent),
                error_base,
            ),
            error_variant_declaration_owner_spec(error_base),
            i,
        );
        let end = i.pos();
        let _ = sequence.trailing_pipe;
        return Recovered::Complete(EnumEqualsVariantBody::Indented(EnumIndentedVariantBody {
            base_indent: error_base,
            block_indent,
            variants: sequence.variants,
            range: equals.end..end,
        }));
    }
    let sequence = parse_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::EqualsInline,
            LayoutDelimitedFrame::inline(error_base),
            error_base,
        ),
        error_variant_declaration_owner_spec(error_base),
        i,
    );
    let end = i.pos();
    Recovered::Complete(EnumEqualsVariantBody::Inline {
        variants: sequence.variants,
        trailing_pipe: sequence.trailing_pipe,
        range: equals.end..end,
    })
}

fn enum_body_implicit_boundary_pending<E>(enum_base: usize, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) || i.input.remainder().is_empty() {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = match mod_trivia(enum_base, i) {
        None => i
            .run(scan_trivia)
            .is_some_and(|trivia| enum_variant_trivia_has_newline(&trivia)),
        Some(_) if i.input.remainder().is_empty() => true,
        Some(_) => i.run(scan_punctuation).is_some_and(|punctuation| {
            matches!(
                punctuation.kind(),
                PunctuationKind::Comma
                    | PunctuationKind::Close(
                        Delimiter::Parenthesis | Delimiter::Bracket | Delimiter::Brace
                    )
            )
        }),
    };
    i.rollback(checkpoint);
    pending
}

fn enum_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_declaration_exact_equals).is_some()
        || i.run(scan_punctuation).is_some_and(|punctuation| {
            matches!(
                punctuation.kind(),
                PunctuationKind::Semicolon
                    | PunctuationKind::Open(Delimiter::Brace)
                    | PunctuationKind::Colon
            )
        });
    i.rollback(checkpoint);
    pending
}

/// Consumes one maximal malformed Enum body-introducer run. The AST path has
/// no recovery nodes yet, but it must reach the same starter or caller-owned
/// boundary that Gate 8's direct-CST adapter will record.
fn enum_body_introducer_error_retry_ast<'source, E>(
    enum_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if enum_body_starter_pending(i) {
            return (start < i.pos()).then_some(true);
        }
        if enum_body_implicit_boundary_pending(enum_base, i) {
            return (start < i.pos()).then_some(false);
        }
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

/// Direct-CST counterpart of [`parse_enum_declaration_isolated`]. It emits
/// only the approved declaration, variant, shared field, and derives CST
/// vocabulary; body-form and sequence facts stay as source-order children
/// after Gate 11 promotes this adapter into public dispatch.
pub(crate) fn commit_enum_declaration_isolated<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: EnumStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    committed.start_node(SyntaxKind::EnumDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::EnumKw, intro.enum_keyword.range());

    let header = commit_required_enum_header_isolated(&intro, committed);
    let header_complete = matches!(header.name, Recovered::Complete(_));
    if header_complete {
        if let Some(start) = committed.probe(|probe| {
            recognize_derives_attachment_start(
                DerivesAttachmentOwner::Enum,
                DerivesAttachmentPosition::Header,
                intro.enum_base,
                probe.input(),
            )
        }) {
            let _ = commit_derives_attachments_isolated(start, committed);
        }
    }

    let has_actual_braced_close =
        header_complete && commit_enum_body_isolated(intro.enum_base, committed);
    if has_actual_braced_close {
        if let Some(start) = committed.probe(|probe| {
            recognize_derives_attachment_start(
                DerivesAttachmentOwner::Enum,
                DerivesAttachmentPosition::Trailing,
                intro.enum_base,
                probe.input(),
            )
        }) {
            let _ = commit_derives_attachments_isolated(start, committed);
        }
    }

    let end = committed_position(committed);
    committed.finish_node();
    committed.probe(|probe| probe.input().errors_rollback(errors_checkpoint));
    Recovered::Complete(intro.start..end)
}

#[derive(Clone)]
enum DirectEnumBodyStarter {
    Bodyless(Range<usize>),
    Braced(Range<usize>),
    Colon(Range<usize>),
    Equals(Range<usize>),
}

fn enum_direct_body_starter<E>(
    enum_base: usize,
    i: &mut SynIn<E>,
) -> Option<(TriviaRun, DirectEnumBodyStarter)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let result = (|| {
        let trivia = mod_trivia(enum_base, i)?;
        if let Some(equals) = i.run(scan_declaration_exact_equals) {
            return Some((trivia, DirectEnumBodyStarter::Equals(equals)));
        }
        let punctuation = i.run(scan_punctuation)?;
        let starter = match punctuation.kind() {
            PunctuationKind::Semicolon => DirectEnumBodyStarter::Bodyless(punctuation.range()),
            PunctuationKind::Open(Delimiter::Brace) => {
                DirectEnumBodyStarter::Braced(punctuation.range())
            }
            PunctuationKind::Colon => DirectEnumBodyStarter::Colon(punctuation.range()),
            _ => return None,
        };
        Some((trivia, starter))
    })();
    i.rollback(checkpoint);
    result
}

/// Emits one complete Enum body form and its one-slot direct-CST recoveries.
/// A clean caller boundary remains the successful implicit-bodyless form;
/// only a non-empty malformed introducer run creates Enum-owned recovery.
fn commit_enum_body_isolated<'parse, 'source, 'local, E, O>(
    enum_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| enum_body_implicit_boundary_pending(enum_base, probe.input())) {
        return false;
    }
    let starter = committed.probe(|probe| enum_direct_body_starter(enum_base, probe.input()));
    let Some((trivia, starter)) = starter else {
        let trivia = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let trivia = mod_trivia(enum_base, i);
            i.rollback(checkpoint);
            trivia
        });
        if let Some(trivia) = trivia {
            let newline = committed
                .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
            if newline {
                return false;
            }
            let consumed = committed
                .probe(|probe| mod_trivia(enum_base, probe.input()))
                .expect("the Enum body-introducer recovery retains its leading trivia");
            assert_eq!(consumed.range(), trivia.range());
            committed.emit_trivia(&consumed);
        }
        match enum_body_introducer_error_retry(enum_base, committed) {
            Some(true) => return commit_enum_body_isolated(enum_base, committed),
            Some(false) | None => return false,
        }
    };
    let consumed_trivia = committed
        .probe(|probe| mod_trivia(enum_base, probe.input()))
        .expect("the selected Enum body starter retains its declaration-continuing trivia");
    assert_eq!(consumed_trivia.range(), trivia.range());
    committed.emit_trivia(&consumed_trivia);

    match starter {
        DirectEnumBodyStarter::Bodyless(range) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("the selected Enum semicolon remains at the cursor");
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Semicolon, range);
            false
        }
        DirectEnumBodyStarter::Braced(range) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("the selected Enum brace remains at the cursor");
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::LBrace, range);
            commit_enum_braced_body_isolated(enum_base, committed)
        }
        DirectEnumBodyStarter::Colon(range) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("the selected Enum colon remains at the cursor");
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Colon, range);
            commit_enum_colon_body_isolated(enum_base, committed);
            false
        }
        DirectEnumBodyStarter::Equals(range) => {
            let equals = committed
                .probe(|probe| probe.input().run(scan_declaration_exact_equals))
                .expect("the selected Enum equals remains at the cursor");
            assert_eq!(equals, range);
            committed.token(SyntaxKind::Equals, range);
            commit_enum_equals_body_isolated(enum_base, committed);
            false
        }
    }
}

fn commit_enum_braced_body_isolated<'parse, 'source, 'local, E, O>(
    enum_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let layout = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let opening = i.run(scan_trivia).expect("trivia scanning is total");
        let layout = LayoutDelimitedFrame::after_opening_trivia(
            enum_base,
            &opening,
            i.local.line().line_indent,
        );
        i.rollback(checkpoint);
        layout
    });
    match commit_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::Braced,
            layout,
            enum_base,
        ),
        enum_variant_declaration_owner_spec(enum_base),
        committed,
    ) {
        EnumVariantSequenceTermination::MatchingClose(_) => true,
        EnumVariantSequenceTermination::MismatchedClose => {
            let range = committed.probe(|probe| {
                let i = probe.input();
                let checkpoint = i.checkpoint();
                let range = i
                    .run(scan_punctuation)
                    .map(|punctuation| punctuation.range());
                i.rollback(checkpoint);
                range.expect("a mismatched Enum brace close remains at the cursor")
            });
            committed.probe(|probe| consume_source_range(range.clone(), probe.input()));
            emit_enum_braced_close_error(range, committed);
            emit_enum_braced_close_missing(committed);
            false
        }
        EnumVariantSequenceTermination::Dedent
        | EnumVariantSequenceTermination::OwnerBoundary
        | EnumVariantSequenceTermination::EndOfInput
        | EnumVariantSequenceTermination::ItemContinuation => {
            emit_enum_braced_close_missing(committed);
            false
        }
    }
}

fn commit_enum_colon_body_isolated<'parse, 'source, 'local, E, O>(
    enum_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    let trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia scanning is total");
    let valid_indent = committed.probe(|probe| {
        enum_variant_trivia_has_newline(&trivia)
            && probe.input().local.line().line_indent > enum_base
    });
    if !valid_indent {
        committed.probe(|probe| probe.input().rollback(checkpoint));
        emit_enum_variant_item_missing(committed);
        return;
    }
    let block_indent = committed.probe(|probe| probe.input().local.line().line_indent);
    committed.emit_trivia(&trivia);
    let _ = commit_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::ColonIndented,
            LayoutDelimitedFrame::inline(block_indent),
            enum_base,
        ),
        enum_variant_declaration_owner_spec(enum_base),
        committed,
    );
}

fn commit_enum_equals_body_isolated<'parse, 'source, 'local, E, O>(
    enum_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    let trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia scanning is total");
    if enum_variant_trivia_has_newline(&trivia) {
        let valid_indent =
            committed.probe(|probe| probe.input().local.line().line_indent > enum_base);
        if !valid_indent {
            committed.probe(|probe| probe.input().rollback(checkpoint));
            emit_enum_variant_item_missing(committed);
            return;
        }
        let block_indent = committed.probe(|probe| probe.input().local.line().line_indent);
        committed.emit_trivia(&trivia);
        let _ = commit_variant_declaration_sequence_with_payload(
            variant_declaration_sequence_spec(
                VariantDeclarationSequenceForm::EqualsIndented,
                LayoutDelimitedFrame::inline(block_indent),
                enum_base,
            ),
            enum_variant_declaration_owner_spec(enum_base),
            committed,
        );
        return;
    }
    committed.emit_trivia(&trivia);
    let _ = commit_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::EqualsInline,
            LayoutDelimitedFrame::inline(enum_base),
            enum_base,
        ),
        enum_variant_declaration_owner_spec(enum_base),
        committed,
    );
}

fn enum_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
    enum_base: usize,
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
        loop {
            let i = probe.input();
            if enum_body_starter_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), true));
            }
            if enum_body_implicit_boundary_pending(enum_base, i) {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            let character = i.input.remainder().chars().next()?;
            if matches!(character, '\r' | '\n') {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            i.input.next()?;
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    })?;
    emit_enum_declaration_error(
        EnumDeclarationRole::BodyIntroducer,
        recovered.0,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Semicolon),
        committed,
    );
    Some(recovered.1)
}

/// Direct-CST counterpart of [`parse_error_declaration_isolated`]. Gate 9
/// promotes this exact adapter into shared statement dispatch.
pub(crate) fn commit_error_declaration_isolated<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: ErrorStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    committed.start_node(SyntaxKind::ErrorDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::ErrorKw, intro.error_keyword.range());
    let header = commit_required_error_header_isolated(&intro, committed);
    let header_complete = matches!(header.name, Recovered::Complete(_));
    if header_complete {
        if let Some(start) = committed.probe(|probe| {
            recognize_derives_attachment_start(
                DerivesAttachmentOwner::Error,
                DerivesAttachmentPosition::Header,
                intro.error_base,
                probe.input(),
            )
        }) {
            let _ = commit_derives_attachments_isolated(start, committed);
        }
    }
    let has_actual_braced_close =
        header_complete && commit_error_body_isolated(intro.error_base, committed);
    if has_actual_braced_close {
        if let Some(start) = committed.probe(|probe| {
            recognize_derives_attachment_start(
                DerivesAttachmentOwner::Error,
                DerivesAttachmentPosition::Trailing,
                intro.error_base,
                probe.input(),
            )
        }) {
            let _ = commit_derives_attachments_isolated(start, committed);
        }
    }
    let end = committed_position(committed);
    committed.finish_node();
    committed.probe(|probe| probe.input().errors_rollback(errors_checkpoint));
    Recovered::Complete(intro.start..end)
}

fn commit_error_body_isolated<'parse, 'source, 'local, E, O>(
    error_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| enum_body_implicit_boundary_pending(error_base, probe.input())) {
        return false;
    }
    let starter = committed.probe(|probe| enum_direct_body_starter(error_base, probe.input()));
    let Some((trivia, starter)) = starter else {
        let trivia = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let trivia = mod_trivia(error_base, i);
            i.rollback(checkpoint);
            trivia
        });
        if let Some(trivia) = trivia {
            let newline = committed
                .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
            if newline {
                return false;
            }
            let consumed = committed
                .probe(|probe| mod_trivia(error_base, probe.input()))
                .expect("the Error body-introducer recovery retains its leading trivia");
            assert_eq!(consumed.range(), trivia.range());
            committed.emit_trivia(&consumed);
        }
        match error_body_introducer_error_retry(error_base, committed) {
            Some(true) => return commit_error_body_isolated(error_base, committed),
            Some(false) | None => return false,
        }
    };
    let consumed_trivia = committed
        .probe(|probe| mod_trivia(error_base, probe.input()))
        .expect("the selected Error body starter retains its declaration-continuing trivia");
    assert_eq!(consumed_trivia.range(), trivia.range());
    committed.emit_trivia(&consumed_trivia);
    match starter {
        DirectEnumBodyStarter::Bodyless(range) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("the selected Error semicolon remains at the cursor");
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Semicolon, range);
            false
        }
        DirectEnumBodyStarter::Braced(range) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("the selected Error brace remains at the cursor");
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::LBrace, range);
            commit_error_braced_body_isolated(error_base, committed)
        }
        DirectEnumBodyStarter::Colon(range) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("the selected Error colon remains at the cursor");
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Colon, range);
            commit_error_colon_body_isolated(error_base, committed);
            false
        }
        DirectEnumBodyStarter::Equals(range) => {
            let equals = committed
                .probe(|probe| probe.input().run(scan_declaration_exact_equals))
                .expect("the selected Error equals remains at the cursor");
            assert_eq!(equals, range);
            committed.token(SyntaxKind::Equals, range);
            commit_error_equals_body_isolated(error_base, committed);
            false
        }
    }
}

fn commit_error_braced_body_isolated<'parse, 'source, 'local, E, O>(
    error_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let layout = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let opening = i.run(scan_trivia).expect("trivia scanning is total");
        let layout = LayoutDelimitedFrame::after_opening_trivia(
            error_base,
            &opening,
            i.local.line().line_indent,
        );
        i.rollback(checkpoint);
        layout
    });
    match commit_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::Braced,
            layout,
            error_base,
        ),
        error_variant_declaration_owner_spec(error_base),
        committed,
    ) {
        EnumVariantSequenceTermination::MatchingClose(_) => true,
        EnumVariantSequenceTermination::MismatchedClose => {
            let range = committed.probe(|probe| {
                let i = probe.input();
                let checkpoint = i.checkpoint();
                let range = i
                    .run(scan_punctuation)
                    .map(|punctuation| punctuation.range());
                i.rollback(checkpoint);
                range.expect("a mismatched Error brace close remains at the cursor")
            });
            committed.probe(|probe| consume_source_range(range.clone(), probe.input()));
            emit_enum_braced_close_error(range, committed);
            emit_enum_braced_close_missing(committed);
            false
        }
        EnumVariantSequenceTermination::Dedent
        | EnumVariantSequenceTermination::OwnerBoundary
        | EnumVariantSequenceTermination::EndOfInput
        | EnumVariantSequenceTermination::ItemContinuation => {
            emit_enum_braced_close_missing(committed);
            false
        }
    }
}

fn commit_error_colon_body_isolated<'parse, 'source, 'local, E, O>(
    error_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    let trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia scanning is total");
    let block_indent = committed.probe(|probe| probe.input().local.line().line_indent);
    if !enum_variant_trivia_has_newline(&trivia) || block_indent <= error_base {
        committed.probe(|probe| probe.input().rollback(checkpoint));
        emit_error_variant_item_missing(committed);
        return;
    }
    committed.emit_trivia(&trivia);
    let _ = commit_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::ColonIndented,
            LayoutDelimitedFrame::inline(block_indent),
            error_base,
        ),
        error_variant_declaration_owner_spec(error_base),
        committed,
    );
}

fn commit_error_equals_body_isolated<'parse, 'source, 'local, E, O>(
    error_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    let trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia scanning is total");
    if enum_variant_trivia_has_newline(&trivia) {
        let block_indent = committed.probe(|probe| probe.input().local.line().line_indent);
        if block_indent <= error_base {
            committed.probe(|probe| probe.input().rollback(checkpoint));
            emit_error_variant_item_missing(committed);
            return;
        }
        committed.emit_trivia(&trivia);
        let _ = commit_variant_declaration_sequence_with_payload(
            variant_declaration_sequence_spec(
                VariantDeclarationSequenceForm::EqualsIndented,
                LayoutDelimitedFrame::inline(block_indent),
                error_base,
            ),
            error_variant_declaration_owner_spec(error_base),
            committed,
        );
        return;
    }
    committed.emit_trivia(&trivia);
    let _ = commit_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::EqualsInline,
            LayoutDelimitedFrame::inline(error_base),
            error_base,
        ),
        error_variant_declaration_owner_spec(error_base),
        committed,
    );
}

fn error_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
    error_base: usize,
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
        loop {
            let i = probe.input();
            if enum_body_starter_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), true));
            }
            if enum_body_implicit_boundary_pending(error_base, i) {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            let character = i.input.remainder().chars().next()?;
            if matches!(character, '\r' | '\n') {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            i.input.next()?;
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    })?;
    emit_error_declaration_error(
        ErrorDeclarationRole::BodyIntroducer,
        recovered.0,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Semicolon),
        committed,
    );
    Some(recovered.1)
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

/// The shared prefix of both nominal and equality Type declarations.  The
/// definition-introducer/RHS phase stays separate so the form judge can see
/// the original post-parameter gap before equality recovery owns it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedTypeDeclarationSharedHeader<'source> {
    name: Recovered<WordSpan<'source>>,
    parameters: Vec<DeclarationTypeParameter<'source>>,
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
) -> (
    ParsedTypeDeclarationHeader<'source>,
    Vec<TypeDeclarationHeaderRecovery>,
)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut recoveries = Vec::new();
    let shared = parse_type_declaration_shared_header_phase(intro, i, &mut recoveries);
    let (equals, rhs_retry) =
        parse_type_declaration_definition_phase(intro, &shared.name, i, &mut recoveries);

    (
        ParsedTypeDeclarationHeader {
            name: shared.name,
            parameters: shared.parameters,
            equals,
            rhs_retry,
        },
        recoveries,
    )
}

fn parse_type_declaration_shared_header_phase<'source, E>(
    intro: &TypeStatementIntro<'source>,
    i: &mut SynIn<'_, 'source, '_, E>,
    recoveries: &mut Vec<TypeDeclarationHeaderRecovery>,
) -> ParsedTypeDeclarationSharedHeader<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let name_boundary = any_ambient_owner_claims(i);
    if !name_boundary {
        let _ = mod_trivia(intro.type_base, i);
    }
    let name = if name_boundary {
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
                    TypeDeclarationInvalidTarget::Equals
                    | TypeDeclarationInvalidTarget::Boundary => Recovered::Incomplete,
                    TypeDeclarationInvalidTarget::Rhs => {
                        unreachable!("name recovery never retries a RHS")
                    }
                }
            }
            None => {
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

    ParsedTypeDeclarationSharedHeader { name, parameters }
}

fn parse_type_declaration_definition_phase<'source, E>(
    intro: &TypeStatementIntro<'source>,
    name: &Recovered<WordSpan<'source>>,
    i: &mut SynIn<'_, 'source, '_, E>,
    recoveries: &mut Vec<TypeDeclarationHeaderRecovery>,
) -> (Recovered<Range<usize>>, bool)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let definition_boundary = any_ambient_owner_claims(i);
    if !definition_boundary {
        let continuation_checkpoint = i.checkpoint();
        if mod_trivia(intro.type_base, i).is_none() {
            i.rollback(continuation_checkpoint);
        }
    }

    if let Some(equals) = i.run(scan_declaration_exact_equals) {
        (Recovered::Complete(equals), true)
    } else if matches!(name, Recovered::Incomplete) {
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
                        let equals = i.run(scan_declaration_exact_equals).expect(
                            "definition-introducer retry must leave exact equals at the cursor",
                        );
                        (Recovered::Complete(equals), true)
                    }
                    TypeDeclarationInvalidTarget::Rhs => (Recovered::Incomplete, true),
                    TypeDeclarationInvalidTarget::Boundary => (Recovered::Incomplete, false),
                    TypeDeclarationInvalidTarget::RawName => {
                        unreachable!(
                            "definition-introducer recovery never retries a declaration name"
                        )
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
    }
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
    let (header, recoveries) =
        committed.probe(|probe| parse_type_declaration_header_slots(intro, probe.input()));
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

/// Gate-7 isolated Type RHS episode.  It extends the already-atomic TD-T
/// state scope with a depth-fenced Derives stop, without changing the public
/// Type continuation before Gate 8.
fn parse_type_declaration_rhs_with_derives_isolated<'source, E>(
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
        .with(StopKind::With)
        .with(StopKind::Derives);
    let scoped_frame = TypeExpressionScopedStopFrame {
        stops: StopSet::default().with(StopKind::Derives),
        visible_episode_depth: i.local.type_expression_episode_depth() + 1,
    };
    i.local.push_indentation_baseline(baseline);
    i.local.push_stop_set(stops);
    i.local.push_type_expression_scoped_stop_frame(scoped_frame);
    let rhs = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_outer_missing_role_and_policy(
                    Some(type_declaration_rhs_role()),
                    TypeExpressionEpisodePolicy::default(),
                    i,
                ),
            )
        }))
        .expect("the mandatory derives-aware Type declaration RHS entry is total");
    assert_eq!(
        i.local.pop_type_expression_scoped_stop_frame(),
        Some(scoped_frame),
    );
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_indentation_baseline(), Some(baseline));

    match rhs {
        Recovered::Complete(rhs) => Recovered::Complete(Box::new(rhs)),
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

fn commit_type_declaration_rhs_with_derives_isolated<'parse, 'source, 'local, E, O>(
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
    let (stops, scoped_frame) = committed.probe(|probe| {
        let i = probe.input();
        (
            i.local
                .stop_set()
                .unwrap_or_default()
                .with(StopKind::Semicolon)
                .with(StopKind::With)
                .with(StopKind::Derives),
            TypeExpressionScopedStopFrame {
                stops: StopSet::default().with(StopKind::Derives),
                visible_episode_depth: i.local.type_expression_episode_depth() + 1,
            },
        )
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_indentation_baseline(baseline);
        i.local.push_stop_set(stops);
        i.local.push_type_expression_scoped_stop_frame(scoped_frame);
    });
    let rhs = commit_direct_type_expression_with_outer_missing_role_and_policy(
        Some(type_declaration_rhs_role()),
        TypeExpressionEpisodePolicy::default(),
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(
            i.local.pop_type_expression_scoped_stop_frame(),
            Some(scoped_frame),
        );
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

/// Parses the shared Type declaration, including header/trailing derives
/// attachments selected by the form-aware promotion core.
pub(crate) fn parse_type_declaration<'source, E>(
    i: SynIn<'_, 'source, '_, E>,
) -> Option<TypeDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_type_declaration_with_derives_isolated(&crate::operator::OperatorTable::empty(), i)
}

/// Operator-aware Type entry used by canonical Statement owners. Attached
/// Impl bodies receive the same table as every other statement-body family.
pub(crate) fn parse_type_declaration_with_operators<'source, E>(
    table: &crate::operator::OperatorTable,
    i: SynIn<'_, 'source, '_, E>,
) -> Option<TypeDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_type_declaration_with_derives_isolated(table, i)
}

/// Direct-CST counterpart of [`parse_type_declaration`], promoted atomically
/// through the same derives-aware core used by the isolated harness.
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
    commit_type_declaration_with_derives_isolated(
        &crate::operator::OperatorTable::empty(),
        committed,
        intro,
    )
    .0
}

/// Operator-aware direct Type entry used by root and canonical Statement
/// owners. The accepted AttachedImpl tail shares their current table.
pub(crate) fn commit_type_declaration_with_operators<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: TypeStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_type_declaration_with_derives_isolated(table, committed, intro).0
}

/// Shared promotion core for Type derives attachments. Header clauses run
/// after the shared name/parameter phase and before TND form selection;
/// trailing clauses run only after a selected Equality RHS episode.
fn parse_type_declaration_with_derives_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<TypeDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let intro = i.run(recognize_type_statement_intro)?;
    let mut recoveries = Vec::new();
    let shared = parse_type_declaration_shared_header_phase(&intro, &mut i, &mut recoveries);
    let mut derives = if matches!(shared.name, Recovered::Complete(_)) {
        recognize_derives_attachment_start(
            DerivesAttachmentOwner::Type,
            DerivesAttachmentPosition::Header,
            intro.type_base,
            &mut i,
        )
        .map(|start| parse_derives_attachments_isolated(start, &mut i))
        .unwrap_or_default()
    } else {
        Vec::new()
    };

    let decision = classify_type_declaration_post_header(&shared.name, intro.type_base, &mut i);
    let form = match decision {
        TypeDeclarationPostHeaderDecision::AttachedImpl(start) => {
            Recovered::Complete(TypeDeclarationForm::AttachedImpl(
                parse_type_attached_impl_isolated(table, start, &mut i),
            ))
        }
        TypeDeclarationPostHeaderDecision::Existing(TypeDeclarationFormDisposition::Nominal {
            owns_trailing_trivia_through,
        }) => {
            consume_type_declaration_nominal_trailing_trivia_until(
                owns_trailing_trivia_through,
                &mut i,
            );
            Recovered::Complete(TypeDeclarationForm::Nominal)
        }
        TypeDeclarationPostHeaderDecision::Existing(
            TypeDeclarationFormDisposition::Equality
            | TypeDeclarationFormDisposition::EqualityRecovery,
        ) => {
            let (equals, rhs_retry) = parse_type_declaration_definition_phase(
                &intro,
                &shared.name,
                &mut i,
                &mut recoveries,
            );
            let header = ParsedTypeDeclarationHeader {
                name: shared.name.clone(),
                parameters: shared.parameters.clone(),
                equals,
                rhs_retry,
            };
            if header.rhs_retry {
                let rhs = parse_type_declaration_rhs_with_derives_isolated(
                    &header,
                    intro.type_base,
                    &mut i,
                );
                if let Some(start) = recognize_derives_attachment_start(
                    DerivesAttachmentOwner::Type,
                    DerivesAttachmentPosition::Trailing,
                    intro.type_base,
                    &mut i,
                ) {
                    derives.extend(parse_derives_attachments_isolated(start, &mut i));
                }
                Recovered::Complete(TypeDeclarationForm::Equality {
                    equals: header.equals,
                    rhs,
                })
            } else {
                Recovered::Incomplete
            }
        }
        TypeDeclarationPostHeaderDecision::Existing(TypeDeclarationFormDisposition::Incomplete) => {
            Recovered::Incomplete
        }
    };
    let range = intro.start..i.pos();
    Some(TypeDeclaration {
        visibility: intro
            .visibility
            .map_or(Visibility::Private, |prefix| prefix.visibility),
        name: shared.name,
        parameters: shared.parameters,
        derives,
        form,
        range,
    })
}

/// Direct-CST counterpart of
/// [`parse_type_declaration_with_derives_isolated`].  It replays each phase
/// only after the shared probes have selected the same AST disposition.
fn commit_type_declaration_with_derives_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: TypeStatementIntro<'source>,
) -> (Recovered<Range<usize>>, Vec<DirectDerivesAttachment>)
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

    let (shared, shared_recoveries, shared_end) = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let mut recoveries = Vec::new();
        let shared = parse_type_declaration_shared_header_phase(&intro, i, &mut recoveries);
        let end = i.pos();
        i.rollback(checkpoint);
        (shared, recoveries, end)
    });
    let shared_surface = ParsedTypeDeclarationHeader {
        name: shared.name.clone(),
        parameters: shared.parameters.clone(),
        equals: Recovered::Incomplete,
        rhs_retry: false,
    };
    commit_type_declaration_header_surface(
        intro.type_base,
        &shared_surface,
        shared_recoveries,
        shared_end,
        committed,
    );

    let mut derives = if matches!(shared.name, Recovered::Complete(_)) {
        committed
            .probe(|probe| {
                recognize_derives_attachment_start(
                    DerivesAttachmentOwner::Type,
                    DerivesAttachmentPosition::Header,
                    intro.type_base,
                    probe.input(),
                )
            })
            .map(|start| commit_derives_attachments_isolated(start, committed))
            .unwrap_or_default()
    } else {
        Vec::new()
    };

    let decision = committed.probe(|probe| {
        classify_type_declaration_post_header(&shared.name, intro.type_base, probe.input())
    });
    match decision {
        TypeDeclarationPostHeaderDecision::AttachedImpl(start) => {
            let _ = commit_type_attached_impl_isolated(table, start, committed);
        }
        TypeDeclarationPostHeaderDecision::Existing(TypeDeclarationFormDisposition::Nominal {
            owns_trailing_trivia_through,
        }) => commit_type_declaration_nominal_trailing_trivia_until(
            owns_trailing_trivia_through,
            committed,
        ),
        TypeDeclarationPostHeaderDecision::Existing(TypeDeclarationFormDisposition::Incomplete) => {
        }
        TypeDeclarationPostHeaderDecision::Existing(
            TypeDeclarationFormDisposition::Equality
            | TypeDeclarationFormDisposition::EqualityRecovery,
        ) => {
            let (header, definition_recoveries, definition_end) = committed.probe(|probe| {
                let i = probe.input();
                let checkpoint = i.checkpoint();
                let mut recoveries = Vec::new();
                let (equals, rhs_retry) = parse_type_declaration_definition_phase(
                    &intro,
                    &shared.name,
                    i,
                    &mut recoveries,
                );
                let end = i.pos();
                i.rollback(checkpoint);
                (
                    ParsedTypeDeclarationHeader {
                        name: shared.name.clone(),
                        parameters: shared.parameters.clone(),
                        equals,
                        rhs_retry,
                    },
                    recoveries,
                    end,
                )
            });
            commit_type_declaration_definition_surface_isolated(
                intro.type_base,
                &header,
                definition_recoveries,
                definition_end,
                committed,
            );
            if header.rhs_retry {
                let _ = commit_type_declaration_rhs_with_derives_isolated(
                    &header,
                    intro.type_base,
                    committed,
                );
                if let Some(start) = committed.probe(|probe| {
                    recognize_derives_attachment_start(
                        DerivesAttachmentOwner::Type,
                        DerivesAttachmentPosition::Trailing,
                        intro.type_base,
                        probe.input(),
                    )
                }) {
                    derives.extend(commit_derives_attachments_isolated(start, committed));
                }
            }
        }
    }

    let end = committed.probe(|probe| probe.input().pos());
    committed.finish_node();
    (Recovered::Complete(intro.start..end), derives)
}

fn commit_type_declaration_definition_surface_isolated<'parse, 'source, 'local, E, O>(
    type_base: usize,
    header: &ParsedTypeDeclarationHeader<'source>,
    recoveries: Vec<TypeDeclarationHeaderRecovery>,
    definition_end: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let definition_recovery = recoveries.iter().find(|recovery| {
        type_declaration_header_recovery_role(recovery)
            == crate::session::TypeDeclarationRole::DefinitionIntroducer
    });
    debug_assert_eq!(recoveries.len(), usize::from(definition_recovery.is_some()));
    let definition_target = definition_recovery
        .map(type_declaration_header_recovery_start)
        .or_else(|| match &header.equals {
            Recovered::Complete(equals) => Some(equals.start),
            Recovered::Incomplete => None,
        })
        .unwrap_or(definition_end);
    commit_type_declaration_continuation_trivia_until(type_base, definition_target, committed);
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
    debug_assert_eq!(committed.probe(|probe| probe.input().pos()), definition_end);
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
        type_declaration_header_recovery_role(recovery) == crate::session::TypeDeclarationRole::Name
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
    commit_type_declaration_continuation_trivia_until(type_base, definition_target, committed);
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

/// Replays only the trailing trivia whose ownership the sink-free nominal form
/// judge already established.  This deliberately does not classify the gap a
/// second time: the reported endpoint is the complete ownership decision.
fn commit_type_declaration_nominal_trailing_trivia_until<'parse, 'source, 'local, E, O>(
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
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("the nominal form judge reported remaining trailing trivia");
    debug_assert_eq!(trivia.range(), current..target);
    committed.emit_trivia(&trivia);
}

/// Consumes only the trailing trivia whose ownership the sink-free nominal
/// form judge already established.  It is replay, not a second form probe.
fn consume_type_declaration_nominal_trailing_trivia_until<E>(target: usize, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let current = i.pos();
    if current == target {
        return;
    }
    let trivia = i
        .run(scan_trivia)
        .expect("the nominal form judge reported remaining trailing trivia");
    debug_assert_eq!(trivia.range(), current..target);
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
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
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

fn declaration_exact_impl_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_word).is_some_and(|word| word.text() == "impl");
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

/// The complete post-header priority decision used by production Type dispatch.
///
/// The `Existing` arm is the explicit insertion seam: a future `with:` form
/// goes before delegation, while a future role-like body belongs inside the
/// existing classifier after Equality and before its terminal dispositions.
#[derive(Clone, Debug, Eq, PartialEq)]
enum TypeDeclarationPostHeaderDecision<'source> {
    AttachedImpl(TypeAttachedImplStart<'source>),
    Existing(TypeDeclarationFormDisposition),
}

/// Exact attached-Impl evidence captured without consuming the Type gap.
#[derive(Clone, Debug, Eq, PartialEq)]
struct TypeAttachedImplStart<'source> {
    leading: TriviaRun,
    keyword: WordSpan<'source>,
    type_base: usize,
}

/// Judges Type's post-header form in TAI-J priority order without committing
/// input, line state, diagnostics, or any rollback-owned local state.
fn classify_type_declaration_post_header<'source, E>(
    name: &Recovered<WordSpan<'source>>,
    type_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> TypeDeclarationPostHeaderDecision<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let attached_impl = if matches!(name, Recovered::Complete(_)) && !any_ambient_owner_claims(i) {
        let leading = i
            .run(scan_trivia)
            .expect("the maximal Type post-header gap scan is total");
        let has_physical_newline = struct_trivia_has_newline(&leading);
        let accepted_continuation = !has_physical_newline
            || (i.local.line().line_indent > type_base
                && !type_stop_is_active_in_current_episode(i, StopKind::Newline)
                && declaration_braced_newline_owner_from_stack(has_physical_newline, i.local)
                    .is_none());
        if accepted_continuation {
            i.run(scan_word)
                .filter(|word| word.text() == "impl")
                .map(|keyword| TypeAttachedImplStart {
                    leading,
                    keyword,
                    type_base,
                })
        } else {
            None
        }
    } else {
        None
    };
    i.rollback(checkpoint);

    attached_impl.map_or_else(
        || {
            // Future `with:` is inserted immediately before this delegation;
            // future role-like bodies are inserted inside the delegated judge
            // after its exact Equality decision.
            TypeDeclarationPostHeaderDecision::Existing(classify_type_declaration_form(
                name, type_base, i,
            ))
        },
        TypeDeclarationPostHeaderDecision::AttachedImpl,
    )
}

/// The isolated nominal-versus-equality disposition after Type's shared name
/// and parameter header.  This is deliberately sink-free until the later
/// dispatch gate selects a committed declaration continuation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeDeclarationFormDisposition {
    /// The exclusive endpoint of terminal trivia the declaration owns.  A
    /// caller-owned boundary reports the shared-header end instead.
    Nominal {
        owns_trailing_trivia_through: usize,
    },
    Equality,
    EqualityRecovery,
    Incomplete,
}

/// A braced statement sequence whose physical newline gives a declaration
/// form or attachment judge terminal authority.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DeclarationBracedNewlineOwner {
    BracedStatementSequence,
    CatchArmSequenceThroughInlineCanonicalStatement,
}

/// Classifies the Type-declaration form without consuming the post-header
/// gap.  The committed nominal/equality continuations remain a later gate.
fn classify_type_declaration_form<'source, E>(
    name: &Recovered<WordSpan<'source>>,
    type_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> TypeDeclarationFormDisposition
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let disposition = if !matches!(name, Recovered::Complete(_)) {
        if type_declaration_exact_equals_after_continuation_pending(type_base, i) {
            TypeDeclarationFormDisposition::EqualityRecovery
        } else {
            TypeDeclarationFormDisposition::Incomplete
        }
    } else {
        let ambient_boundary = any_ambient_owner_claims(i);
        if ambient_boundary {
            TypeDeclarationFormDisposition::Nominal {
                owns_trailing_trivia_through: i.pos(),
            }
        } else {
            let gap_checkpoint = i.checkpoint();
            let shared_end = i.pos();
            let trivia = i
                .run(scan_trivia)
                .expect("the maximal Type form gap trivia scan is total");
            let has_physical_newline = i.input.source()[trivia.range()].contains(['\r', '\n']);
            let accepted_continuation =
                !has_physical_newline || i.local.line().line_indent > type_base;
            let disposition = if accepted_continuation && declaration_exact_equals_pending(i) {
                TypeDeclarationFormDisposition::Equality
            } else {
                let owns_trailing_trivia_through =
                    if declaration_braced_newline_owner_from_stack(has_physical_newline, i.local)
                        .is_some()
                    {
                        Some(shared_end)
                    } else {
                        type_declaration_nominal_terminal_trivia_end_after_trivia(
                            type_base,
                            shared_end,
                            has_physical_newline,
                            i,
                        )
                    };
                match owns_trailing_trivia_through {
                    Some(owns_trailing_trivia_through) => TypeDeclarationFormDisposition::Nominal {
                        owns_trailing_trivia_through,
                    },
                    None => TypeDeclarationFormDisposition::EqualityRecovery,
                }
            };
            i.rollback(gap_checkpoint);
            disposition
        }
    };
    i.rollback(checkpoint);
    disposition
}

/// Probes an exact lone `=` after Type's ordinary continuation trivia.
fn type_declaration_exact_equals_after_continuation_pending<E>(
    type_base: usize,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let accepted = mod_trivia(type_base, i).is_some() && declaration_exact_equals_pending(i);
    i.rollback(checkpoint);
    accepted
}

/// Reads the ambient owner stack without changing it.  A braced statement
/// block owns its own physical-newline statement boundary; a catch barrier
/// does so only after crossing an inline canonical arm-body frame.
fn declaration_braced_newline_owner<E>(i: &mut SynIn<E>) -> Option<DeclarationBracedNewlineOwner>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let has_physical_newline = i
        .run(scan_trivia)
        .is_some_and(|trivia| i.input.source()[trivia.range()].contains(['\r', '\n']));
    let owner = declaration_braced_newline_owner_from_stack(has_physical_newline, i.local);
    i.rollback(checkpoint);
    owner
}

fn declaration_braced_newline_owner_from_stack(
    has_physical_newline: bool,
    local: &ParseLocal,
) -> Option<DeclarationBracedNewlineOwner> {
    if !has_physical_newline {
        return None;
    }
    declaration_braced_newline_owner_for_physical_newline(local)
}

fn declaration_braced_newline_owner_for_physical_newline(
    local: &ParseLocal,
) -> Option<DeclarationBracedNewlineOwner> {
    let mut skipped_inline = 0;
    for frame in local.ambient_owner_scope_frames() {
        match frame.kind() {
            AmbientOwnerScopeKind::InlineCanonicalStatement(_) => skipped_inline += 1,
            AmbientOwnerScopeKind::BracedBarrier(
                BracedBarrierOrigin::BracedStatementBlockExpression,
            ) => {
                return Some(DeclarationBracedNewlineOwner::BracedStatementSequence);
            }
            AmbientOwnerScopeKind::BracedBarrier(BracedBarrierOrigin::CatchBracedArmSequence) => {
                return (skipped_inline > 0).then_some(
                    DeclarationBracedNewlineOwner::CatchArmSequenceThroughInlineCanonicalStatement,
                );
            }
            AmbientOwnerScopeKind::RootStatement | AmbientOwnerScopeKind::IndentedStatement => {
                return None;
            }
        }
    }
    None
}

/// The non-ambient terminal alternatives for a complete nominal header.
fn type_declaration_nominal_terminal_trivia_end_after_trivia<E>(
    type_base: usize,
    shared_end: usize,
    has_physical_newline: bool,
    i: &mut SynIn<E>,
) -> Option<usize>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if has_physical_newline && i.local.line().line_indent <= type_base {
        // The entire equal-or-shallower physical gap belongs to the caller,
        // even when that newline is immediately followed by EOF.
        Some(shared_end)
    } else if i.input.remainder().is_empty() {
        // Empty/same-line terminal trivia and maximal strictly-deeper
        // trailing trivia both end a nominal declaration at EOF.  In these
        // EOF cases the declaration owns the already-probed gap.
        Some(i.pos())
    } else if matches!(i.input.remainder().chars().next(), Some(';')) {
        (!has_physical_newline).then_some(i.pos())
    } else {
        type_declaration_active_fixed_statement_boundary_pending(i).then_some(shared_end)
    }
}

/// Active caller punctuation has statement-boundary authority only for this
/// fixed subset; semicolon remains its own terminal alternative above.
fn type_declaration_active_fixed_statement_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        let stop = match punctuation.kind() {
            PunctuationKind::Comma => StopKind::Comma,
            PunctuationKind::Close(crate::session::Delimiter::Parenthesis) => {
                StopKind::RightParenthesis
            }
            PunctuationKind::Close(crate::session::Delimiter::Bracket) => StopKind::RightBracket,
            PunctuationKind::Close(crate::session::Delimiter::Brace) => StopKind::RightBrace,
            _ => return false,
        };
        i.local.stop_set().is_some_and(|stops| stops.contains(stop))
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
    let base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
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
    Some(ModStatementIntro {
        start,
        visibility,
        after_visibility,
        mod_keyword: keyword,
    })
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
            let selected_as_use =
                scan_required_inline_trivia(i).is_some() && parse_use_tree(i).is_some();
            i.rollback(use_checkpoint);
            return !selected_as_use;
        }
        if target_head.text() == "mod" {
            return false;
        }
        if matches!(
            target_head.text(),
            "lazy" | "prefix" | "infix" | "suffix" | "nullfix"
        ) {
            let definition_checkpoint = i.checkpoint();
            let binding_base = i
                .local
                .indentation_baseline()
                .map_or(0, |baseline| baseline.column);
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
        probe
            .input()
            .local
            .indentation_baseline()
            .map_or(0, |baseline| baseline.column)
    });
    let target_trivia = committed.probe(|probe| binding_trivia(binding_base, probe.input()));
    if let Some(trivia) = &target_trivia {
        committed.emit_trivia(trivia);
    }
    let stops = committed.probe(|probe| {
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
            .with(StopKind::Equal)
    });
    committed.probe(|probe| probe.input().local.push_stop_set(stops));
    let target = parse_direct_pattern_with_outer_missing_role(
        operators,
        LeadingTrivia::None,
        Some(GrammarRole::Declaration(DeclarationRole::Binding(
            BindingRole::Target,
        ))),
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
        ParsedBindingDefinition {
            equals: equals.clone(),
            body,
            range: equals.start..end,
        }
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
        let base = committed.probe(|probe| {
            probe
                .input()
                .local
                .indentation_baseline()
                .map_or(0, |baseline| baseline.column)
        });
        let _ = base;
    }
    committed.token(SyntaxKind::ModKw, intro.mod_keyword.range());
    let mod_base = committed.probe(|probe| {
        probe
            .input()
            .local
            .indentation_baseline()
            .map_or(0, |baseline| baseline.column)
    });
    if let Some(trivia) = committed.probe(|probe| mod_trivia(mod_base, probe.input())) {
        committed.emit_trivia(&trivia);
    }

    let mut identity_missing = false;
    let mut identity_error = false;
    let first =
        commit_word(committed).or_else(|| match mod_word_error_retry(committed, ModRole::Name) {
            Some(true) => commit_word(committed),
            Some(false) => {
                identity_error = true;
                None
            }
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
            let name = commit_word(committed).or_else(|| {
                match mod_word_error_retry(committed, ModRole::TestName) {
                    Some(true) => commit_word(committed),
                    Some(false) => {
                        identity_error = true;
                        None
                    }
                    None => None,
                }
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
        let starter = i
            .run(scan_punctuation)
            .and_then(|punctuation| match punctuation.kind() {
                PunctuationKind::Semicolon => Some(PunctuationKind::Semicolon),
                PunctuationKind::Open(Delimiter::Brace) => {
                    Some(PunctuationKind::Open(Delimiter::Brace))
                }
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
                let starter =
                    i.run(scan_punctuation)
                        .and_then(|punctuation| match punctuation.kind() {
                            PunctuationKind::Semicolon => Some(PunctuationKind::Semicolon),
                            PunctuationKind::Open(Delimiter::Brace) => {
                                Some(PunctuationKind::Open(Delimiter::Brace))
                            }
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
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("accepted starter remains");
            committed.token(SyntaxKind::Semicolon, punctuation.range());
        }
        Some(PunctuationKind::Open(Delimiter::Brace)) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("accepted starter remains");
            commit_braced_statement_block_expression(operators, punctuation.range(), committed);
        }
        Some(PunctuationKind::Colon) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("accepted starter remains");
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

/// Commits the selected Struct declaration through the derives-aware
/// promotion core. The selected keyword is never returned to later choices.
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
    commit_struct_declaration_with_derives_isolated(committed, intro).0
}

/// Direct-CST counterpart of
/// [`parse_struct_declaration_with_derives_isolated`]. The public entry and
/// the focused harness both use this one attachment-owning core.
fn commit_struct_declaration_with_derives_isolated<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: StructStatementIntro<'source>,
) -> (Recovered<()>, Vec<DirectDerivesAttachment>)
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
    if let Some(trivia) =
        committed.probe(|probe| struct_continuation_trivia(intro.struct_base, probe.input()))
    {
        committed.emit_trivia(&trivia);
    }

    let mut name_incomplete = false;
    if let Some(name) = commit_word(committed) {
        committed.token(SyntaxKind::Identifier, name.range());
    } else {
        let recovery = struct_name_error_retry(committed);
        match recovery {
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
                emit_struct_missing(
                    committed,
                    crate::session::StructRole::Name,
                    ExpectedSyntax::Identifier,
                );
            }
        }
    }

    let mut derives = if !name_incomplete {
        committed
            .probe(|probe| {
                recognize_derives_attachment_start(
                    DerivesAttachmentOwner::Struct,
                    DerivesAttachmentPosition::Header,
                    intro.struct_base,
                    probe.input(),
                )
            })
            .map(|start| commit_derives_attachments_isolated(start, committed))
            .unwrap_or_default()
    } else {
        Vec::new()
    };

    let body_starter_pending = committed.probe(|probe| struct_body_starter_pending(probe.input()));
    let mut body_starter = None;
    if !name_incomplete || body_starter_pending {
        if let Some(trivia) =
            committed.probe(|probe| struct_continuation_trivia(intro.struct_base, probe.input()))
        {
            committed.emit_trivia(&trivia);
        }
        body_starter = committed.probe(|probe| struct_body_starter(probe.input()));
        commit_struct_body_introducer(intro.struct_base, committed);
    }
    if committed_struct_body_has_actual_trailing_close(committed, body_starter) {
        if let Some(start) = committed.probe(|probe| {
            recognize_derives_attachment_start(
                DerivesAttachmentOwner::Struct,
                DerivesAttachmentPosition::Trailing,
                intro.struct_base,
                probe.input(),
            )
        }) {
            derives.extend(commit_derives_attachments_isolated(start, committed));
        }
    }
    committed.finish_node();
    (Recovered::Complete(()), derives)
}

fn committed_struct_body_has_actual_trailing_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    starter: Option<StructBodyStarter>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let expected_close = match starter {
            Some(StructBodyStarter::NamedBraced(_)) => b'}',
            Some(StructBodyStarter::Tuple(_)) => b')',
            Some(StructBodyStarter::Bodyless(_) | StructBodyStarter::NamedIndented(_)) | None => {
                return false;
            }
        };
        i.pos() > 0 && i.input.source().as_bytes().get(i.pos() - 1) == Some(&expected_close)
    })
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
    let opening =
        committed.probe(|probe| consume_struct_indented_opening(struct_base, probe.input()));
    let Some((opening, block_indent)) = opening else {
        emit_struct_missing(
            committed,
            crate::session::StructRole::Field,
            ExpectedSyntax::Identifier,
        );
        return;
    };
    committed.emit_trivia(&opening);
    let stops = committed.probe(|probe| {
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
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
        if committed
            .probe(|probe| struct_indented_terminal_boundary_pending(block_indent, probe.input()))
        {
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
                StructIndentedGap::Trivia(_)
                    if committed.probe(|probe| {
                        struct_indented_terminal_boundary_pending(block_indent, probe.input())
                    }) =>
                {
                    break;
                }
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
            if let Some(run) =
                committed.probe(|probe| scan_struct_field_invalid_run(false, probe.input()))
            {
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
        let StructIndentedGap::Trivia(trivia) = gap else {
            unreachable!()
        };
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
                StructIndentedGap::Trivia(_)
                    if committed.probe(|probe| {
                        struct_indented_terminal_boundary_pending(block_indent, probe.input())
                    }) =>
                {
                    break;
                }
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
        if committed
            .probe(|probe| struct_indented_terminal_boundary_pending(block_indent, probe.input()))
        {
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
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
            .without(StopKind::Newline)
            .with(StopKind::Comma)
            .with(StopKind::RightParenthesis)
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_delimiter(Delimiter::Parenthesis);
        i.local.push_stop_set(stops);
    });
    let opening = committed
        .probe(|probe| probe.input().run(scan_trivia))
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
        if let Some((range, actual)) = committed
            .probe(|probe| scan_struct_mismatched_close_for(Delimiter::Parenthesis, probe.input()))
        {
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
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
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
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
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
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
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
        let trivia = committed
            .probe(|probe| probe.input().run(scan_trivia))
            .expect("trivia is total");
        committed.emit_trivia(&trivia);
        if let Some(comma) = committed.probe(|probe| scan_struct_comma(probe.input())) {
            committed.token(SyntaxKind::Comma, comma);
            let post = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&post);
            if let Some(close) =
                committed.probe(|probe| scan_struct_close_parenthesis(probe.input()))
            {
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
        if let Some((range, actual)) = committed
            .probe(|probe| scan_struct_mismatched_close_for(Delimiter::Parenthesis, probe.input()))
        {
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
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
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
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
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
    commit_variant_tuple_field(VariantFieldDriverSpec::Struct, committed);
}

fn commit_struct_tuple_field<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_variant_tuple_field(VariantFieldDriverSpec::Struct, committed);
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
        PunctuationKind::Open(Delimiter::Brace) => {
            StructBodyStarter::NamedBraced(punctuation.range())
        }
        PunctuationKind::Open(Delimiter::Parenthesis) => {
            StructBodyStarter::Tuple(punctuation.range())
        }
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
    let trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia is total");
    let newline = committed
        .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
    if newline && committed.probe(|probe| probe.input().local.line().line_indent <= mod_base) {
        committed.probe(|probe| probe.input().rollback(checkpoint));
        emit_mod_missing(committed, ModRole::Body, ExpectedSyntax::Statement);
        return;
    }
    if newline {
        let indent = committed.probe(|probe| probe.input().local.line().line_indent);
        commit_indented_mod_body(operators, trivia, mod_base, indent, committed);
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
    let mut statement_committed =
        commit_canonical_statement(operators, LeadingTrivia::None, committed);
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
    commit_binding_style_body(
        operators,
        binding_base,
        GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Body)),
        |expression| ParsedBindingBody::new(expression.range()),
        |trivia, block_indent, committed| {
            commit_indented_binding_body(operators, trivia, binding_base, block_indent, committed);
            let end = committed.probe(|probe| probe.input().pos());
            ParsedBindingBody::new(body_start..end)
        },
        |committed| {
            direct_expression_error_retry(
                operators,
                GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Body)),
                committed,
            )
            .then_some(BindingStyleInlineRecovery::Retry)
            .unwrap_or(BindingStyleInlineRecovery::None)
        },
        committed,
    )
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

/// Emits the one owner-selected Missing record for a mandatory Binding-style
/// expression body after its layout decision has reached a terminal boundary.
fn emit_expression_missing_with_role<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: GrammarRole,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
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
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Semicolon,
                    ),
                    range: at..at,
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Open(Delimiter::Brace),
                    ),
                    range: at..at,
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Colon,
                    ),
                    range: at..at,
                    sources: source,
                },
            ]),
            0,
        )
    });
    committed.emit_missing(record);
}

/// Emits the one outer-body recovery owned by an accepted Impl tail. The AST
/// path represents the same terminal slot as `ImplBody::Incomplete`; direct
/// CST additionally materializes the owner-mapped missing recovery node.
fn emit_impl_tail_body_introducer_missing<'parse, 'source, 'local, E, O>(
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = owner_spec.grammar_role(ImplRole::BodyIntroducer);
        let source = ExpectationSources::COMMITTED_RECOVERY_RULE;
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
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Semicolon,
                    ),
                    range: at..at,
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Open(Delimiter::Brace),
                    ),
                    range: at..at,
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Colon,
                    ),
                    range: at..at,
                    sources: source,
                },
            ]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_impl_tail_body_missing<'parse, 'source, 'local, E, O>(
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_impl_tail_missing(
        owner_spec,
        committed,
        ImplRole::Body,
        ExpectedSyntax::Statement,
    );
}

fn emit_impl_tail_missing<'parse, 'source, 'local, E, O>(
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: ImplRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = owner_spec.grammar_role(role);
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
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_impl_tail_error<'parse, 'source, 'local, E, O>(
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    impl_role: ImplRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = owner_spec.grammar_role(impl_role);
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
                expected,
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

/// Emits the one outer-body recovery owned by an accepted Role declaration.
fn emit_role_body_introducer_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Declaration(DeclarationRole::Role(
            crate::session::RoleDeclarationRole::BodyIntroducer,
        ));
        let source = ExpectationSources::COMMITTED_RECOVERY_RULE;
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
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Semicolon,
                    ),
                    range: at..at,
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Open(Delimiter::Brace),
                    ),
                    range: at..at,
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Colon,
                    ),
                    range: at..at,
                    sources: source,
                },
            ]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_role_body_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_role_missing(
        committed,
        crate::session::RoleDeclarationRole::Body,
        ExpectedSyntax::Statement,
    );
}

fn emit_role_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: crate::session::RoleDeclarationRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Declaration(DeclarationRole::Role(role));
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
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_role_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: crate::session::RoleDeclarationRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Role(role));
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
                expected,
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

/// Emits the one outer-body recovery owned by an accepted Act declaration.
/// A complete Act tail-nothing form never reaches this emitter: it is a
/// successful implicit bodyless form, not a missing body introducer.
fn emit_act_body_introducer_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Declaration(DeclarationRole::Act(
            crate::session::ActDeclarationRole::BodyIntroducer,
        ));
        let source = ExpectationSources::COMMITTED_RECOVERY_RULE;
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
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Semicolon,
                    ),
                    range: at..at,
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Open(Delimiter::Brace),
                    ),
                    range: at..at,
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Colon,
                    ),
                    range: at..at,
                    sources: source,
                },
            ]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_act_body_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_act_missing(
        committed,
        crate::session::ActDeclarationRole::Body,
        ExpectedSyntax::Statement,
    );
}

fn emit_act_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    act_role: crate::session::ActDeclarationRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Declaration(DeclarationRole::Act(act_role));
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
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_act_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    act_role: crate::session::ActDeclarationRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Act(act_role));
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
                expected,
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
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
            RecoverySiteKey {
                role,
                range: at..at,
            },
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
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Semicolon,
                    ),
                    range: at..at,
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Open(Delimiter::Brace),
                    ),
                    range: at..at,
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Open(Delimiter::Parenthesis),
                    ),
                    range: at..at,
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Colon,
                    ),
                    range: at..at,
                    sources: source,
                },
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
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Semicolon,
                    ),
                    range: range.clone(),
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Open(Delimiter::Brace),
                    ),
                    range: range.clone(),
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Open(Delimiter::Parenthesis),
                    ),
                    range: range.clone(),
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Colon,
                    ),
                    range: range.clone(),
                    sources: source,
                },
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
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
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
            RecoverySiteKey {
                role: grammar_role,
                range: range.clone(),
            },
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
            if matches!(
                character,
                '\r' | '\n' | ';' | ',' | ')' | ']' | '}' | '{' | ':'
            ) {
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
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Semicolon,
                    ),
                    range: range.clone(),
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Open(Delimiter::Brace),
                    ),
                    range: range.clone(),
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Colon,
                    ),
                    range,
                    sources: source,
                },
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
            if matches!(
                character,
                '\r' | '\n' | ';' | ',' | ')' | ']' | '}' | '{' | ':'
            ) {
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
    pub(crate) fn equals(&self) -> Range<usize> {
        self.equals.clone()
    }
    pub(crate) fn body(&self) -> &Recovered<BindingBody<'source>> {
        &self.body
    }
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum BindingBody<'source> {
    Inline {
        expression: OperatorChain<'source>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
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
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ModBody<'source> {
    Bodyless {
        semicolon: Range<usize>,
    },
    Braced {
        block: BracedStatementBlockExpression<'source>,
    },
    Colon {
        colon: Recovered<Range<usize>>,
        body: Recovered<ModColonBody<'source>>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ModColonBody<'source> {
    Inline {
        statement: Box<Statement<'source>>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
}

/// A standalone Impl declaration shared by root and canonical Statements.
///
/// Gate 1 establishes only the approved AST shape. Recognition and body
/// parsing remain unreachable until their later dedicated gates.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ImplDeclaration<'source> {
    visibility: Visibility,
    head: Recovered<Box<TypeExpression<'source>>>,
    description: Option<ImplDescription<'source>>,
    body: Recovered<ImplBody<'source>>,
    range: Range<usize>,
}

impl ImplDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ImplDescription<'source> {
    colon: Range<usize>,
    value: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ImplBody<'source> {
    Bodyless {
        semicolon: Range<usize>,
    },
    Braced {
        block: BracedStatementBlockExpression<'source>,
    },
    Colon {
        colon: Range<usize>,
        body: Recovered<ImplColonBody<'source>>,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ImplColonBody<'source> {
    Inline {
        statement: Box<Statement<'source>>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
}

/// A standalone Role declaration shared by root and canonical Statements.
///
/// Gate 1 establishes only the approved AST shape. Recognition and body
/// parsing remain unreachable until their later dedicated gates.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RoleDeclaration<'source> {
    visibility: Visibility,
    head: Recovered<Box<TypeExpression<'source>>>,
    body: Recovered<RoleBody<'source>>,
    range: Range<usize>,
}

impl RoleDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RoleBody<'source> {
    Bodyless {
        semicolon: Range<usize>,
    },
    Braced {
        block: BracedStatementBlockExpression<'source>,
    },
    Colon {
        colon: Range<usize>,
        body: Recovered<RoleColonBody<'source>>,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RoleColonBody<'source> {
    Inline {
        statement: Box<Statement<'source>>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
}

/// A standalone Act declaration shared by root and canonical Statements.
///
/// Gate 1 establishes only the approved AST shape. Recognition and body
/// parsing remain unreachable until their later dedicated gates.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ActDeclaration<'source> {
    visibility: Visibility,
    head: Recovered<Box<TypeExpression<'source>>>,
    source: Option<ActSourceClause<'source>>,
    derives: Vec<DerivesAttachment<'source>>,
    body: Recovered<ActBody<'source>>,
    range: Range<usize>,
}

impl ActDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ActSourceClause<'source> {
    equals: Range<usize>,
    source: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ActBody<'source> {
    Bodyless {
        semicolon: Option<Range<usize>>,
    },
    Braced {
        block: BracedStatementBlockExpression<'source>,
    },
    Colon {
        colon: Range<usize>,
        body: Recovered<ActColonBody<'source>>,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ActColonBody<'source> {
    Inline {
        statement: Box<Statement<'source>>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
}

/// A standalone Cast declaration shared by root and canonical Statements.
///
/// Gate 1 establishes only the approved AST shape. Recognition and body
/// parsing remain unreachable until their later dedicated gates.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CastDeclaration<'source> {
    visibility: Visibility,
    pattern: Recovered<CastPattern<'source>>,
    target: Recovered<CastTarget<'source>>,
    form: Recovered<CastForm<'source>>,
    range: Range<usize>,
}

impl CastDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CastPattern<'source> {
    open: Recovered<Range<usize>>,
    value: Recovered<Box<Pattern<'source>>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CastTarget<'source> {
    colon: Recovered<Range<usize>>,
    value: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum CastForm<'source> {
    Bodyless {
        semicolon: Range<usize>,
    },
    Definition {
        equals: Range<usize>,
        body: Recovered<CastBody<'source>>,
        range: Range<usize>,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum CastBody<'source> {
    Inline {
        expression: OperatorChain<'source>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
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
    derives: Vec<DerivesAttachment<'source>>,
    body: Recovered<StructBody<'source>>,
    range: Range<usize>,
}

impl StructDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

/// A standalone Enum declaration shared by root and canonical Statements.
///
/// Gate 1 establishes only the approved AST shape. Recognition, variant
/// parsing, and body parsing remain unreachable until their later dedicated
/// gates.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EnumDeclaration<'source> {
    visibility: Visibility,
    name: Recovered<WordSpan<'source>>,
    parameters: Vec<DeclarationTypeParameter<'source>>,
    derives: Vec<DerivesAttachment<'source>>,
    body: Recovered<EnumBody<'source>>,
    range: Range<usize>,
}

impl EnumDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

/// A standalone Error declaration shared by root and canonical Statements.
///
/// Gate 1 establishes only the approved AST shape. Recognition, variant
/// parsing, and body parsing remain unreachable until their later dedicated
/// gates.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ErrorDeclaration<'source> {
    visibility: Visibility,
    name: Recovered<WordSpan<'source>>,
    parameters: Vec<DeclarationTypeParameter<'source>>,
    derives: Vec<DerivesAttachment<'source>>,
    body: Recovered<EnumBody<'source>>,
    range: Range<usize>,
}

impl ErrorDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum EnumBody<'source> {
    Bodyless {
        semicolon: Option<Range<usize>>,
    },
    Braced(EnumBracedBody<'source>),
    Colon {
        colon: Range<usize>,
        body: Recovered<EnumIndentedVariantBody<'source>>,
    },
    Equals {
        equals: Range<usize>,
        body: Recovered<EnumEqualsVariantBody<'source>>,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EnumBracedBody<'source> {
    open: Range<usize>,
    variants: Vec<Recovered<EnumVariant<'source>>>,
    trailing_comma: Option<Range<usize>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum EnumEqualsVariantBody<'source> {
    Inline {
        variants: Vec<Recovered<EnumVariant<'source>>>,
        trailing_pipe: Option<Range<usize>>,
        range: Range<usize>,
    },
    Indented(EnumIndentedVariantBody<'source>),
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EnumIndentedVariantBody<'source> {
    base_indent: usize,
    block_indent: usize,
    variants: Vec<Recovered<EnumVariant<'source>>>,
    range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EnumVariant<'source> {
    name: Recovered<WordSpan<'source>>,
    payload: EnumVariantPayload<'source>,
    range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum EnumVariantPayload<'source> {
    Unit,
    From {
        keyword: Range<usize>,
        type_expr: Recovered<Box<TypeExpression<'source>>>,
        range: Range<usize>,
    },
    Named {
        open: Range<usize>,
        fields: Vec<Recovered<StructNamedField<'source>>>,
        trailing_comma: Option<Range<usize>>,
        close: Recovered<Range<usize>>,
        range: Range<usize>,
    },
    Tuple {
        open: Range<usize>,
        fields: Vec<Recovered<StructTupleField<'source>>>,
        trailing_comma: Option<Range<usize>>,
        close: Recovered<Range<usize>>,
        range: Range<usize>,
    },
    Positional {
        types: Vec<Recovered<Box<TypeExpression<'source>>>>,
        range: Range<usize>,
    },
}

/// A parser-side Type declaration.  Its form remains syntax-only: alias,
/// nominal, and opaque semantics belong to later HIR ownership.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypeDeclaration<'source> {
    visibility: Visibility,
    name: Recovered<WordSpan<'source>>,
    parameters: Vec<DeclarationTypeParameter<'source>>,
    derives: Vec<DerivesAttachment<'source>>,
    form: Recovered<TypeDeclarationForm<'source>>,
    range: Range<usize>,
}

impl TypeDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TypeDeclarationForm<'source> {
    Nominal,
    Equality {
        equals: Recovered<Range<usize>>,
        rhs: Recovered<Box<TypeExpression<'source>>>,
    },
    AttachedImpl(TypeAttachedImpl<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypeAttachedImpl<'source> {
    impl_keyword: Range<usize>,
    head: Recovered<Box<TypeExpression<'source>>>,
    description: Option<ImplDescription<'source>>,
    body: Recovered<ImplBody<'source>>,
    range: Range<usize>,
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
        from_fn(parse_enum_declaration_isolated).map(Declaration::Enum),
        from_fn(parse_error_declaration_isolated).map(Declaration::Error),
        parse_type_declaration.map(Declaration::Type),
        from_fn(|i| parse_role_declaration_isolated(&crate::operator::OperatorTable::empty(), i))
            .map(Declaration::Role),
        from_fn(|i| parse_impl_declaration_isolated(&crate::operator::OperatorTable::empty(), i))
            .map(Declaration::Impl),
        from_fn(|i| {
            parse_cast_declaration_form_aware_isolated(&crate::operator::OperatorTable::empty(), i)
        })
        .map(Declaration::Cast),
        from_fn(|i| parse_act_declaration_isolated(&crate::operator::OperatorTable::empty(), i))
            .map(Declaration::Act),
        from_fn(|i| parse_for_statement_isolated(&crate::operator::OperatorTable::empty(), i))
            .map(Declaration::For),
        parse_use_declaration.map(Declaration::Use),
        parse_operator_header.map(Declaration::OperatorHeader),
        parse_binding_declaration.map(Declaration::Binding),
        from_fn(|i| {
            parse_mod_declaration_with_operators(&crate::operator::OperatorTable::empty(), i)
        })
        .map(Declaration::Mod),
    ))
}

/// Parses the Struct declaration through the derives-aware promotion core.
pub(crate) fn parse_struct_declaration<'source, E>(
    i: SynIn<'_, 'source, '_, E>,
) -> Option<StructDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_struct_declaration_with_derives_isolated(i)
}

/// Shared promotion core for Struct derives attachments. Keeping header/body
/// ownership here gives the public entry and focused harness one code path.
fn parse_struct_declaration_with_derives_isolated<'source, E>(
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
            Some(false) | None => {
                name_incomplete = true;
                Recovered::Incomplete
            }
        }
    };

    let mut derives = if matches!(name, Recovered::Complete(_)) {
        recognize_derives_attachment_start(
            DerivesAttachmentOwner::Struct,
            DerivesAttachmentPosition::Header,
            intro.struct_base,
            &mut i,
        )
        .map(|start| parse_derives_attachments_isolated(start, &mut i))
        .unwrap_or_default()
    } else {
        Vec::new()
    };

    let body_starter_pending = struct_body_starter_pending(&mut i);
    let body = if !name_incomplete || body_starter_pending {
        let _ = struct_continuation_trivia(intro.struct_base, &mut i);
        parse_struct_body_ast(intro.struct_base, &mut i)
            .map_or(Recovered::Incomplete, Recovered::Complete)
    } else {
        Recovered::Incomplete
    };
    if struct_body_has_actual_trailing_close(&body) {
        if let Some(start) = recognize_derives_attachment_start(
            DerivesAttachmentOwner::Struct,
            DerivesAttachmentPosition::Trailing,
            intro.struct_base,
            &mut i,
        ) {
            derives.extend(parse_derives_attachments_isolated(start, &mut i));
        }
    }

    let body_end = match &body {
        Recovered::Complete(StructBody::Bodyless { semicolon }) => semicolon.end,
        Recovered::Complete(StructBody::NamedBraced(body)) => body.range.end,
        Recovered::Complete(StructBody::NamedIndented(body)) => body.range.end,
        Recovered::Complete(StructBody::Tuple(body)) => body.range.end,
        Recovered::Incomplete => match &name {
            Recovered::Complete(name) => name.range().end,
            Recovered::Incomplete => intro.struct_keyword.range().end,
        },
    };
    let derives_end = derives
        .last()
        .map_or(0, |attachment| attachment.clause.range.end);
    Some(StructDeclaration {
        visibility: intro
            .visibility
            .map_or(Visibility::Private, |prefix| prefix.visibility),
        name,
        derives,
        body,
        range: intro.start..body_end.max(derives_end),
    })
}

fn struct_body_has_actual_trailing_close(body: &Recovered<StructBody<'_>>) -> bool {
    matches!(
        body,
        Recovered::Complete(StructBody::NamedBraced(StructNamedBracedBody {
            close: Recovered::Complete(_),
            ..
        })) | Recovered::Complete(StructBody::Tuple(StructTupleBody {
            close: Recovered::Complete(_),
            ..
        }))
    )
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
    let punctuation = i
        .run(scan_punctuation)
        .expect("a selected Struct body starter remains available");
    match starter {
        StructBodyStarter::Bodyless(range) => {
            debug_assert_eq!(punctuation.range(), range);
            Some(StructBody::Bodyless { semicolon: range })
        }
        StructBodyStarter::NamedBraced(range) => {
            debug_assert_eq!(punctuation.range(), range);
            Some(StructBody::NamedBraced(parse_struct_named_braced_body_ast(
                struct_base,
                range,
                i,
            )))
        }
        StructBodyStarter::Tuple(range) => {
            debug_assert_eq!(punctuation.range(), range);
            Some(StructBody::Tuple(parse_struct_tuple_body_ast(
                struct_base,
                range,
                i,
            )))
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
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
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
                StructIndentedGap::Trivia(_)
                    if struct_indented_terminal_boundary_pending(block_indent, i) =>
                {
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
        let StructIndentedGap::Trivia(trivia) = gap else {
            unreachable!()
        };
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
                StructIndentedGap::Trivia(_)
                    if struct_indented_terminal_boundary_pending(block_indent, i) =>
                {
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
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
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

        fields.push(parse_variant_tuple_field_ast(
            VariantFieldDriverSpec::Struct,
            i,
        ));

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
    StructTupleBody {
        open: open.clone(),
        fields,
        trailing_comma,
        close,
        range: open.start..end,
    }
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
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
        .without(StopKind::Newline)
        .with(StopKind::Comma)
        .with(StopKind::RightBrace);
    i.local.push_delimiter(Delimiter::Brace);
    i.local.push_stop_set(stops);
    let opening = i.run(scan_trivia).expect("trivia is total");
    let layout =
        LayoutDelimitedFrame::after_opening_trivia(incoming, &opening, i.local.line().line_indent);
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
    StructNamedBracedBody {
        open: open.clone(),
        fields,
        trailing_comma,
        close,
        range: open.start..end,
    }
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
    parse_variant_named_field_ast(VariantFieldDriverSpec::Struct, ambient_sensitive, i)
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
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
            .without(StopKind::Newline)
            .with(StopKind::Comma)
            .with(StopKind::RightBrace)
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_delimiter(Delimiter::Brace);
        i.local.push_stop_set(stops);
    });
    let opening = committed
        .probe(|probe| probe.input().run(scan_trivia))
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
        if let Some((range, actual)) =
            committed.probe(|probe| scan_struct_mismatched_close(probe.input()))
        {
            emit_struct_mismatched_close(committed, range, actual);
            // Keep recovery at the close slot: trivia after a consumed local
            // mismatch precedes the next close retry, not a field slot.
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close(committed);
                break;
            }
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
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
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
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
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if !commit_struct_named_field(true, committed) {
            if let Some(run) =
                committed.probe(|probe| scan_struct_field_invalid_run(false, probe.input()))
            {
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
                let trivia = committed
                    .probe(|probe| probe.input().run(scan_trivia))
                    .expect("trivia is total");
                committed.emit_trivia(&trivia);
                continue;
            } else {
                emit_struct_missing(
                    committed,
                    crate::session::StructRole::Field,
                    ExpectedSyntax::Identifier,
                );
                break;
            }
        }

        if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
            emit_struct_missing_close(committed);
            break;
        }
        let trivia = committed
            .probe(|probe| probe.input().run(scan_trivia))
            .expect("trivia is total");
        committed.emit_trivia(&trivia);
        if let Some(comma) = committed.probe(|probe| scan_struct_comma(probe.input())) {
            committed.token(SyntaxKind::Comma, comma);
            let post = committed
                .probe(|probe| probe.input().run(scan_trivia))
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
                emit_struct_missing(
                    committed,
                    crate::session::StructRole::Field,
                    ExpectedSyntax::Identifier,
                );
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
                emit_struct_missing(
                    committed,
                    crate::session::StructRole::Field,
                    ExpectedSyntax::Identifier,
                );
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
        if let Some((range, actual)) =
            committed.probe(|probe| scan_struct_mismatched_close(probe.input()))
        {
            emit_struct_mismatched_close(committed, range, actual);
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close(committed);
                break;
            }
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
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
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
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
    emit_struct_missing(
        committed,
        crate::session::StructRole::Field,
        ExpectedSyntax::Identifier,
    );
    committed.finish_node();
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum VariantFieldRecoverySlot {
    Item,
    Name,
    Colon,
    Type,
    Separator,
}

fn variant_field_recovery_role(
    spec: VariantFieldDriverSpec,
    slot: VariantFieldRecoverySlot,
) -> GrammarRole {
    match (spec, slot) {
        (VariantFieldDriverSpec::Struct, VariantFieldRecoverySlot::Item) => {
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::Field))
        }
        (VariantFieldDriverSpec::Struct, VariantFieldRecoverySlot::Name) => {
            GrammarRole::Declaration(DeclarationRole::Struct(
                crate::session::StructRole::FieldName,
            ))
        }
        (VariantFieldDriverSpec::Struct, VariantFieldRecoverySlot::Colon) => {
            GrammarRole::Declaration(DeclarationRole::Struct(
                crate::session::StructRole::FieldColon,
            ))
        }
        (VariantFieldDriverSpec::Struct, VariantFieldRecoverySlot::Type) => {
            GrammarRole::Declaration(DeclarationRole::Struct(
                crate::session::StructRole::FieldType,
            ))
        }
        (VariantFieldDriverSpec::Struct, VariantFieldRecoverySlot::Separator) => {
            GrammarRole::Declaration(DeclarationRole::Struct(
                crate::session::StructRole::FieldSeparator,
            ))
        }
        (VariantFieldDriverSpec::EnumNamed, VariantFieldRecoverySlot::Item) => {
            GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Variant(
                VariantDeclarationRole::NamedField,
            )))
        }
        (VariantFieldDriverSpec::EnumNamed, VariantFieldRecoverySlot::Name) => {
            GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldName,
            )))
        }
        (VariantFieldDriverSpec::EnumNamed, VariantFieldRecoverySlot::Colon) => {
            GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldColon,
            )))
        }
        (VariantFieldDriverSpec::EnumNamed, VariantFieldRecoverySlot::Type) => {
            GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldType,
            )))
        }
        (VariantFieldDriverSpec::EnumNamed, VariantFieldRecoverySlot::Separator) => {
            GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldSeparator,
            )))
        }
        (VariantFieldDriverSpec::EnumTuple, _) => GrammarRole::Declaration(DeclarationRole::Enum(
            EnumDeclarationRole::Variant(VariantDeclarationRole::TupleFieldType),
        )),
        (VariantFieldDriverSpec::ErrorNamed, VariantFieldRecoverySlot::Item) => {
            GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::NamedField,
            )))
        }
        (VariantFieldDriverSpec::ErrorNamed, VariantFieldRecoverySlot::Name) => {
            GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldName,
            )))
        }
        (VariantFieldDriverSpec::ErrorNamed, VariantFieldRecoverySlot::Colon) => {
            GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldColon,
            )))
        }
        (VariantFieldDriverSpec::ErrorNamed, VariantFieldRecoverySlot::Type) => {
            GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldType,
            )))
        }
        (VariantFieldDriverSpec::ErrorNamed, VariantFieldRecoverySlot::Separator) => {
            GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldSeparator,
            )))
        }
        (VariantFieldDriverSpec::ErrorTuple, _) => {
            GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::TupleFieldType,
            )))
        }
    }
}

fn emit_variant_field_missing<'parse, 'source, 'local, E, O>(
    spec: VariantFieldDriverSpec,
    slot: VariantFieldRecoverySlot,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = variant_field_recovery_role(spec, slot);
        let at = i.pos();
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
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_variant_field_error<'parse, 'source, 'local, E, O>(
    spec: VariantFieldDriverSpec,
    slot: VariantFieldRecoverySlot,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = variant_field_recovery_role(spec, slot);
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
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

/// The owner-parameterized direct field item core.  Struct reaches it through
/// its existing wrapper, so its node order and `StructRole` records remain
/// unchanged; Enum selects the corresponding Variant roles instead.
fn commit_variant_named_field<'parse, 'source, 'local, E, O>(
    spec: VariantFieldDriverSpec,
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
        if let Some(trivia) =
            committed.probe(|probe| consume_struct_field_name_trivia(probe.input()))
        {
            committed.emit_trivia(&trivia);
        }
    } else {
        match malformed_name {
            Some(StructFieldInvalidRun {
                range,
                target: StructFieldInvalidTarget::Colon { trivia },
            }) => {
                emit_variant_field_error(
                    spec,
                    VariantFieldRecoverySlot::Name,
                    committed,
                    range,
                    ExpectedSyntax::Identifier,
                );
                if let Some(trivia) = trivia {
                    committed.emit_trivia(&trivia);
                }
            }
            _ => emit_variant_field_missing(
                spec,
                VariantFieldRecoverySlot::Name,
                committed,
                ExpectedSyntax::Identifier,
            ),
        }
    }
    let colon =
        colon_without_name.or_else(|| committed.probe(|probe| scan_struct_colon(probe.input())));
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
                emit_variant_field_error(
                    spec,
                    VariantFieldRecoverySlot::Colon,
                    committed,
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
                emit_variant_field_missing(
                    spec,
                    VariantFieldRecoverySlot::Colon,
                    committed,
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
        emit_variant_field_missing(
            spec,
            VariantFieldRecoverySlot::Type,
            committed,
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
        i.local.push_type_delimited_owner(spec.named_type_owner());
    });
    let _ =
        commit_direct_type_expression_with_outer_missing_role(Some(spec.type_role()), committed);
    committed.probe(|probe| {
        assert_eq!(
            probe.input().local.pop_type_delimited_owner(),
            Some(spec.named_type_owner()),
        );
    });
    committed.finish_node();
    true
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
    commit_variant_named_field(VariantFieldDriverSpec::Struct, ambient_sensitive, committed)
}

fn push_struct_layout<E>(layout: LayoutDelimitedFrame, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    i.local.push_indentation_baseline(IndentationBaseline {
        column: layout.base_indent(),
        kind: IndentationBaselineKind::Introducer,
    });
}

fn pop_struct_layout<E>(layout: LayoutDelimitedFrame, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    assert_eq!(
        i.local.pop_indentation_baseline(),
        Some(IndentationBaseline {
            column: layout.base_indent(),
            kind: IndentationBaselineKind::Introducer
        }),
    );
}

fn push_struct_indented_layout<E>(block_indent: usize, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    i.local.push_indentation_baseline(IndentationBaseline {
        column: block_indent,
        kind: IndentationBaselineKind::Block,
    });
}

fn pop_struct_indented_layout<E>(block_indent: usize, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
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
fn consume_struct_indented_gap<E>(block_indent: usize, i: &mut SynIn<E>) -> StructIndentedGap
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

fn struct_indented_terminal_boundary_pending<E>(block_indent: usize, i: &mut SynIn<E>) -> bool
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
    let base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
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
        if end == start
            && (struct_colon_pending(i) || (allow_type_primary && struct_type_primary_pending(i)))
        {
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
                    return Some(StructFieldInvalidRun {
                        range: start..end,
                        target: StructFieldInvalidTarget::Boundary,
                    });
                }
                if struct_colon_pending(i) {
                    return Some(StructFieldInvalidRun {
                        range: start..end,
                        target: StructFieldInvalidTarget::Colon {
                            trivia: Some(trivia),
                        },
                    });
                }
                if allow_type_primary && struct_type_primary_pending(i) {
                    return Some(StructFieldInvalidRun {
                        range: start..end,
                        target: StructFieldInvalidTarget::TypePrimary {
                            trivia: Some(trivia),
                        },
                    });
                }
                i.rollback(checkpoint);
                return Some(StructFieldInvalidRun {
                    range: start..end,
                    target: StructFieldInvalidTarget::Boundary,
                });
            }
            if struct_field_boundary_pending(i) || struct_mismatched_close_pending(i) {
                return Some(StructFieldInvalidRun {
                    range: start..end,
                    target: StructFieldInvalidTarget::Boundary,
                });
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
fn scan_struct_field_name_colon_recovery<E>(i: &mut SynIn<E>) -> Option<StructFieldInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let recovered = scan_struct_field_invalid_run(false, i);
    if matches!(
        recovered,
        Some(StructFieldInvalidRun {
            target: StructFieldInvalidTarget::Colon { .. },
            ..
        })
    ) {
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

fn struct_outer_owned_mismatched_close_pending_for<E>(expected: Delimiter, i: &mut SynIn<E>) -> bool
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
    trivia
        .parts()
        .iter()
        .any(|part| matches!(part.kind(), TriviaPartKind::Newline))
}

fn emit_struct_missing_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_struct_missing_close_for(
        committed,
        ConstructRole::StructNamedFields,
        Delimiter::Brace,
    );
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
        let role = GrammarRole::ClosingDelimiter { owner, delimiter };
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
        let role = GrammarRole::ClosingDelimiter { owner, delimiter };
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
                    delimiter,
                )),
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
                expected,
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn struct_name_error_retry_ast<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<bool>
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
    let binding_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    binding_trivia(binding_base, &mut i)?;
    let stops = i.local.stop_set().unwrap_or_default().with(StopKind::Equal);
    i.local.push_stop_set(stops);
    let target_role = GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Target));
    let target = i.run(from_fn(|i| {
        parse_pattern_with_outer_missing_role(table, Some(target_role), i)
    }));
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
            Some(BindingDefinition {
                equals,
                body,
                range: body_start..end,
            })
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
    let mod_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
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
                let name = i
                    .run(scan_word)
                    .map_or(Recovered::Incomplete, Recovered::Complete);
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
    Some(ModDeclaration {
        visibility,
        test_marker,
        name,
        body,
        range: start..end,
    })
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
    let ambient_scope = i.local.push_inline_canonical_statement_ambient_scope(
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
                body: Recovered::Complete(ModColonBody::Inline {
                    statement: Box::new(statement),
                }),
            });
        }
        if mod_statement_error_retry_ast(table, i).is_some_and(|retry| retry) {
            let statement = parse_mod_inline_statement_ast(table, i)?;
            return Some(ModBody::Colon {
                colon: Recovered::Incomplete,
                body: Recovered::Complete(ModColonBody::Inline {
                    statement: Box::new(statement),
                }),
            });
        }
        if i.pos() == start {
            i.rollback(checkpoint);
        }
        return None;
    };
    match punctuation.kind() {
        PunctuationKind::Semicolon => Some(ModBody::Bodyless {
            semicolon: punctuation.range(),
        }),
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
                    body: Recovered::Complete(ModColonBody::Inline {
                        statement: Box::new(statement),
                    }),
                });
            }
            if mod_statement_error_retry_ast(table, i).is_some_and(|retry| retry) {
                let statement = parse_mod_inline_statement_ast(table, i)?;
                return Some(ModBody::Colon {
                    colon: Recovered::Incomplete,
                    body: Recovered::Complete(ModColonBody::Inline {
                        statement: Box::new(statement),
                    }),
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
    let ambient_scope = i.local.push_inline_canonical_statement_ambient_scope(
        crate::session::InlineStatementOwnerKind::ModColonBody,
    );
    let statement = if let Some(statement) = i.run(from_fn(|i| parse_canonical_statement(table, i)))
    {
        Some(statement)
    } else if mod_statement_error_retry_ast(table, i).is_some_and(|retry| retry) {
        i.run(from_fn(|i| parse_canonical_statement(table, i)))
    } else {
        None
    };
    let body = statement.map(|statement| {
        let terminal = i.checkpoint();
        if i.run(scan_punctuation)
            .is_none_or(|punctuation| punctuation.kind() != PunctuationKind::Semicolon)
        {
            i.rollback(terminal);
        }
        ModColonBody::Inline {
            statement: Box::new(statement),
        }
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
        if matches!(
            character,
            '\r' | '\n' | ';' | ',' | ')' | ']' | '}' | '{' | ':'
        ) {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        let checkpoint = i.checkpoint();
        let candidate = i
            .run(from_fn(|i| parse_canonical_statement(table, i)))
            .is_some();
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
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Semicolon
                | PunctuationKind::Open(Delimiter::Brace)
                | PunctuationKind::Colon
        )
    });
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
    if i.input.source()[trivia.range()].contains(['\r', '\n'])
        && i.local.line().line_indent <= mod_base
    {
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
    parse_binding_style_body(
        binding_base,
        |_trivia, i| {
            i.run(from_fn(|i| parse_expression_with_operators(table, i)))
                .map(|expression| BindingBody::Inline { expression })
        },
        |trivia, block_indent, i| BindingBody::Indented {
            block: parse_indented_binding_body(table, trivia, binding_base, block_indent, i),
        },
        i,
    )
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
fn scan_declaration_exact_equals<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    while i
        .input
        .remainder()
        .chars()
        .next()
        .is_some_and(declaration_operator_character)
    {
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
        && !matches!(
            character,
            '(' | ')' | '[' | ']' | '{' | '}' | ',' | ':' | '/' | ';' | '\\' | '\'' | '@'
        )
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
mod tests;

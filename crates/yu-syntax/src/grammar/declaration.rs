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

mod act_decl;
mod binding_style_body;
mod cast_decl;
mod derives;
mod enum_decl;
mod error_decl;
mod for_statement;
mod impl_decl;
mod operator_header;
mod role_decl;
mod struct_decl;
mod type_decl;
mod use_decl;
mod variant_core;

use act_decl::*;
use binding_style_body::*;
use cast_decl::*;
use derives::*;
use enum_decl::*;
use error_decl::*;
use for_statement::*;
use impl_decl::*;
use operator_header::*;
use role_decl::*;
use struct_decl::*;
use type_decl::*;
use use_decl::*;
use variant_core::*;

pub(crate) use act_decl::{
    ActDeclaration, commit_act_declaration_isolated, parse_act_declaration_isolated,
};
pub(crate) use cast_decl::{
    CastDeclaration, commit_cast_declaration_isolated, parse_cast_declaration_form_aware_isolated,
};
pub(crate) use enum_decl::{
    EnumDeclaration, commit_enum_declaration_isolated, parse_enum_declaration_isolated,
};
pub(crate) use error_decl::{
    ErrorDeclaration, commit_error_declaration_isolated, parse_error_declaration_isolated,
};
pub(crate) use for_statement::{
    ForStatement, commit_for_statement_isolated, parse_for_statement_isolated,
};
pub(crate) use impl_decl::{
    ImplDeclaration, commit_impl_declaration_isolated, parse_impl_declaration_isolated,
};
pub(crate) use role_decl::{
    RoleDeclaration, commit_role_declaration_isolated, parse_role_declaration_isolated,
};
pub(crate) use struct_decl::{
    StructDeclaration, commit_struct_declaration, parse_struct_declaration,
};
pub(crate) use type_decl::{
    TypeDeclaration, commit_type_declaration_with_operators, parse_type_declaration_with_operators,
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

/// A braced statement sequence whose physical newline gives a declaration
/// form or attachment judge terminal authority.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DeclarationBracedNewlineOwner {
    BracedStatementSequence,
    CatchArmSequenceThroughInlineCanonicalStatement,
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DeclarationTypeParameter<'source> {
    Identifier(WordSpan<'source>),
    SigilIdentifier(WordSpan<'source>),
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

fn struct_trivia_has_newline(trivia: &TriviaRun) -> bool {
    trivia
        .parts()
        .iter()
        .any(|part| matches!(part.kind(), TriviaPartKind::Newline))
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

//! Central hub for declaration grammar: shared vocabulary, root dispatch, and plumbing.
//!
//! Declaration families live in child modules; this module keeps their common wiring.

use std::{ops::Range, sync::Arc};

use chasa::{
    Back as _, ErrorSink, Input as _,
    error::std::{Unexpected, UnexpectedEndOfInput},
    input::IsCut,
    parser::Parser as _,
    prelude::{In, from_fn, item},
};

use crate::grammar::type_expr::{
    commit_direct_type_expression_with_handoff_recovery_isolated,
    parse_required_type_expression_with_handoff_recovery_isolated,
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
mod binding_decl;
mod binding_style_body;
mod cast_decl;
mod companion;
mod derives;
mod enum_decl;
mod error_decl;
mod for_statement;
mod impl_decl;
mod mod_decl;
mod operator_header;
mod role_decl;
mod struct_decl;
mod type_decl;
mod use_decl;
mod variant_core;

use act_decl::*;
use binding_decl::*;
use binding_style_body::*;
use cast_decl::*;
use companion::*;
use derives::*;
use enum_decl::*;
use error_decl::*;
use for_statement::*;
use impl_decl::*;
use mod_decl::*;
use operator_header::*;
use role_decl::*;
use struct_decl::*;
use type_decl::*;
use use_decl::*;
use variant_core::*;

pub(crate) use act_decl::{
    ActDeclaration, commit_act_declaration_isolated, parse_act_declaration_isolated,
};
pub(crate) use binding_decl::{
    BindingDeclaration, commit_binding_declaration, parse_binding_declaration_with_operators,
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
pub(crate) use mod_decl::{
    ModDeclaration, commit_mod_declaration, parse_mod_declaration_with_operators,
};
pub(crate) use role_decl::{
    RoleDeclaration, commit_role_declaration_isolated, parse_role_declaration_isolated,
};
pub(crate) use struct_decl::{
    StructDeclaration, commit_struct_declaration, commit_struct_declaration_with_operators,
    parse_struct_declaration, parse_struct_declaration_with_operators,
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

/// A committed continuation completed its CST regardless of whether it could
/// produce the semantic value required by its caller.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Recovered<T> {
    Complete(T),
    Incomplete,
}

/// Sink-free evidence that an eligible declaration owner may hand exact
/// `with` to the isolated declaration-companion adapter. The gap and word
/// remain owned by the later adapter on every outcome.
pub(super) fn recognize_declaration_companion_handoff<E>(
    owner_base: usize,
    i: &mut SynIn<E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let errors_checkpoint = i.errors_checkpoint();
    let handoff = (|| {
        if i.input.remainder().is_empty()
            || any_ambient_owner_claims(i)
            || derives_active_fixed_boundary_pending(i)
        {
            return None;
        }
        let trivia = mod_trivia(owner_base, i)?;
        if trivia.is_empty()
            || i.input.remainder().is_empty()
            || any_ambient_owner_claims(i)
            || derives_active_fixed_boundary_pending(i)
        {
            return None;
        }
        let word = i.run(scan_word)?;
        (word.text() == "with").then(|| word.range())
    })();
    i.rollback(checkpoint);
    i.errors_rollback(errors_checkpoint);
    handoff
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct VisibilityPrefix<'source> {
    visibility: Visibility,
    keyword: WordSpan<'source>,
}

/// A module declaration has the same child shape at root and in a canonical
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DeclarationTypeParameter<'source> {
    Identifier(WordSpan<'source>),
    SigilIdentifier(WordSpan<'source>),
}

/// A braced statement sequence whose physical newline gives a declaration
/// form or attachment judge terminal authority.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DeclarationBracedNewlineOwner {
    BracedStatementSequence,
    CatchArmSequenceThroughInlineCanonicalStatement,
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
                let _ = commit_struct_declaration_with_operators(operators, &mut committed, intro);
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
                BracedBarrierOrigin::BracedStatementBlockExpression
                | BracedBarrierOrigin::DeclarationCompanion,
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

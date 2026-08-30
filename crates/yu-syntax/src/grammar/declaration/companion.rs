use std::{ops::Range, sync::Arc};

use chasa::{
    ErrorSink,
    error::std::{Unexpected, UnexpectedEndOfInput},
    prelude::from_fn,
};

use crate::{
    grammar::expression::{
        Statement, StatementSequenceSeparator, canonical_statement_invalid_run,
        commit_canonical_statement, commit_declaration_companion_braced_missing_separator,
        commit_declaration_companion_braced_separator,
        commit_declaration_companion_indented_separator,
        declaration_companion_braced_boundary_pending,
        declaration_companion_indented_terminal_boundary, parse_canonical_statement,
        recognize_declaration_companion_braced_missing_separator,
        recognize_declaration_companion_braced_separator,
        recognize_declaration_companion_indented_separator,
    },
    operator::OperatorTable,
    scan::operator::LeadingTrivia,
    session::{
        CommitOutput, Committed, CommittedRecoveryRecord, DeclarationCompanionRole,
        DeclarationRole, ExpectationSources, ExpectedSyntax, GrammarRole, RecoveryKind,
        RecoverySiteKey, SynIn, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use super::{DerivesClause, Recovered};

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DeclarationCompanion<'source> {
    pub(super) keyword: Range<usize>,
    pub(super) form: DeclarationCompanionForm<'source>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DeclarationCompanionForm<'source> {
    Colon {
        colon: Recovered<Range<usize>>,
        body: Recovered<DeclarationCompanionColonBody<'source>>,
    },
    Braced {
        open: Range<usize>,
        items: Vec<Recovered<DeclarationCompanionItem<'source>>>,
        close: Recovered<Range<usize>>,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DeclarationCompanionColonBody<'source> {
    Inline {
        item: Box<DeclarationCompanionItem<'source>>,
        semicolon: Option<Range<usize>>,
    },
    Indented(DeclarationCompanionIndentedBody<'source>),
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DeclarationCompanionIndentedBody<'source> {
    pub(super) base_indent: usize,
    pub(super) block_indent: usize,
    pub(super) items: Vec<Recovered<DeclarationCompanionItem<'source>>>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DeclarationCompanionItem<'source> {
    Statement(Box<Statement<'source>>),
    Derives(Vec<DerivesClause<'source>>),
}

/// Parses the mandatory statement-only sequence of a future indented
/// declaration companion. Gate 2 deliberately leaves this adapter
/// production-unreachable; Gate 3 owns companion form recognition and scope.
#[allow(dead_code)]
pub(super) fn parse_indented_declaration_companion_statement_items<'source, E>(
    table: &OperatorTable,
    block_indent: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Vec<Recovered<DeclarationCompanionItem<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut items = vec![parse_declaration_companion_statement_item(table, i)];
    loop {
        let Some(separator) = recognize_declaration_companion_indented_separator(block_indent, i)
        else {
            break;
        };
        if separator.is_semicolon()
            && declaration_companion_indented_terminal_boundary(i, block_indent)
        {
            break;
        }
        items.push(parse_declaration_companion_statement_item(table, i));
    }
    items
}

/// Parses the empty-allowed statement-only sequence of a future braced
/// declaration companion without consuming its closing or outer boundary.
#[allow(dead_code)]
pub(super) fn parse_braced_declaration_companion_statement_items<'source, E>(
    table: &OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Vec<Recovered<DeclarationCompanionItem<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if declaration_companion_braced_boundary_pending(i) {
        return Vec::new();
    }
    let mut items = vec![parse_declaration_companion_statement_item(table, i)];
    loop {
        if declaration_companion_braced_boundary_pending(i) {
            break;
        }
        let Some(transition) = recognize_braced_companion_statement_transition(table, i) else {
            break;
        };
        if matches!(transition, BracedCompanionStatementTransition::Separator(_))
            && declaration_companion_braced_boundary_pending(i)
        {
            break;
        }
        items.push(parse_declaration_companion_statement_item(table, i));
    }
    items
}

/// Direct-CST counterpart of
/// [`parse_indented_declaration_companion_statement_items`].
#[allow(dead_code)]
pub(super) fn commit_indented_declaration_companion_statement_items<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    block_indent: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_declaration_companion_statement_item(
        table,
        declaration_companion_indented_item_role(),
        LeadingTrivia::None,
        committed,
    );
    loop {
        let Some(separator) =
            commit_declaration_companion_indented_separator(block_indent, committed)
        else {
            break;
        };
        if separator.is_semicolon()
            && committed.probe(|probe| {
                declaration_companion_indented_terminal_boundary(probe.input(), block_indent)
            })
        {
            break;
        }
        commit_declaration_companion_statement_item(
            table,
            declaration_companion_indented_item_role(),
            separator.following_leading_trivia(),
            committed,
        );
    }
}

/// Direct-CST counterpart of
/// [`parse_braced_declaration_companion_statement_items`].
#[allow(dead_code)]
pub(super) fn commit_braced_declaration_companion_statement_items<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| declaration_companion_braced_boundary_pending(probe.input())) {
        return;
    }
    commit_declaration_companion_statement_item(
        table,
        declaration_companion_item_role(),
        LeadingTrivia::None,
        committed,
    );
    loop {
        if committed.probe(|probe| declaration_companion_braced_boundary_pending(probe.input())) {
            return;
        }
        let leading = if let Some(separator) =
            commit_declaration_companion_braced_separator(committed)
        {
            let leading = separator.following_leading_trivia();
            if committed.probe(|probe| declaration_companion_braced_boundary_pending(probe.input()))
            {
                return;
            }
            leading
        } else if let Some(leading) =
            commit_declaration_companion_braced_missing_separator(table, committed)
        {
            emit_declaration_companion_missing(
                declaration_companion_separator_role(),
                ExpectedSyntax::StatementSeparator,
                committed,
            );
            leading
        } else {
            return;
        };
        commit_declaration_companion_statement_item(
            table,
            declaration_companion_item_role(),
            leading,
            committed,
        );
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum DeclarationCompanionStatementRecovery {
    Malformed { range: Range<usize>, retry: bool },
    Missing,
}

/// One sink-free failure decision is shared by all four companion adapters.
/// Normal items first take the unconditional canonical Statement path.  Only
/// a failed canonical parse/commit reaches this classifier, which advances one
/// maximal malformed episode to either a retry candidate or a retained
/// sequence boundary.
fn declaration_companion_statement_recovery<E>(
    table: &OperatorTable,
    i: &mut SynIn<E>,
) -> DeclarationCompanionStatementRecovery
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    canonical_statement_invalid_run(table, i).map_or(
        DeclarationCompanionStatementRecovery::Missing,
        |(range, retry)| DeclarationCompanionStatementRecovery::Malformed { range, retry },
    )
}

fn parse_declaration_companion_statement_item<'source, E>(
    table: &OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<DeclarationCompanionItem<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    if let Some(statement) = i.run(from_fn(|i| parse_canonical_statement(table, i))) {
        return Recovered::Complete(DeclarationCompanionItem::Statement(Box::new(statement)));
    }
    i.errors_rollback(errors_checkpoint);
    match declaration_companion_statement_recovery(table, i) {
        DeclarationCompanionStatementRecovery::Malformed { retry: true, .. } => {
            let statement = i
                .run(from_fn(|i| parse_canonical_statement(table, i)))
                .expect("a retried companion Statement candidate must parse canonically");
            Recovered::Complete(DeclarationCompanionItem::Statement(Box::new(statement)))
        }
        DeclarationCompanionStatementRecovery::Malformed { retry: false, .. }
        | DeclarationCompanionStatementRecovery::Missing => Recovered::Incomplete,
    }
}

fn commit_declaration_companion_statement_item<'parse, 'source, 'local, E, O>(
    table: &OperatorTable,
    role: GrammarRole,
    leading: LeadingTrivia,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::Statement);
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    if !commit_canonical_statement(table, leading, committed) {
        committed.probe(|probe| probe.input().errors_rollback(errors_checkpoint));
        match committed
            .probe(|probe| declaration_companion_statement_recovery(table, probe.input()))
        {
            DeclarationCompanionStatementRecovery::Malformed { range, retry } => {
                emit_declaration_companion_error(role, ExpectedSyntax::Statement, range, committed);
                if retry {
                    assert!(commit_canonical_statement(
                        table,
                        LeadingTrivia::None,
                        committed,
                    ));
                }
            }
            DeclarationCompanionStatementRecovery::Missing => {
                emit_declaration_companion_missing(role, ExpectedSyntax::Statement, committed);
            }
        }
    }
    committed.finish_node();
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum BracedCompanionStatementTransition {
    Separator(StatementSequenceSeparator),
    MissingSeparator { leading: LeadingTrivia },
}

fn recognize_braced_companion_statement_transition<E>(
    table: &OperatorTable,
    i: &mut SynIn<E>,
) -> Option<BracedCompanionStatementTransition>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(separator) = recognize_declaration_companion_braced_separator(i) {
        return Some(BracedCompanionStatementTransition::Separator(separator));
    }
    recognize_declaration_companion_braced_missing_separator(table, i)
        .map(|leading| BracedCompanionStatementTransition::MissingSeparator { leading })
}

fn emit_declaration_companion_missing<'parse, 'source, 'local, E, O>(
    role: GrammarRole,
    expected: ExpectedSyntax,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
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

fn emit_declaration_companion_error<'parse, 'source, 'local, E, O>(
    role: GrammarRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
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
                category: UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

fn declaration_companion_item_role() -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Companion(DeclarationCompanionRole::Item))
}

fn declaration_companion_indented_item_role() -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Companion(
        DeclarationCompanionRole::IndentedItem,
    ))
}

fn declaration_companion_separator_role() -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Companion(
        DeclarationCompanionRole::Separator,
    ))
}

#[cfg(test)]
mod tests {
    use std::{hint::black_box, ops::Range, sync::Arc};

    use chasa::{input::IsCut, prelude::In};

    use crate::{
        SyntaxNode,
        grammar::expression::{
            canonical_statement_candidate_input_calls,
            reset_canonical_statement_candidate_input_calls,
        },
        input::SourceInput,
        operator::{BindingPower, OperatorDeclaration, OperatorFixities},
        session::{
            CommittedRecoveryRecord, Delimiter, EmbeddedLexicalMode, ExpressionDelimitedOwner,
            FullCstOutput, GrammarRole, IndentationBaseline, IndentationBaselineKind,
            InlineStatementOwnerKind, LineState, OperatorCandidateProbe, ParseLocal,
            ParseLocalValueSnapshot, Probe, RecoveryKind, StagedHeaderFact, StopKind, StopSet,
            TypeDelimitedOwner, TypeExpressionEpisodePolicy, TypeExpressionScopedStopFrame,
            TypeMalformedCallerBoundaryFence,
        },
    };

    use super::*;

    #[derive(Debug)]
    struct AstOutcome {
        complete: Vec<bool>,
        remainder: String,
        before: ParseLocalValueSnapshot,
        after: ParseLocalValueSnapshot,
        sink_clean: bool,
        cut: bool,
    }

    #[derive(Debug)]
    struct DirectOutcome {
        statement_count: usize,
        remainder: String,
        recoveries: Vec<CommittedRecoveryRecord>,
        emitted: String,
        child_kinds: Vec<SyntaxKind>,
        node_kinds: Vec<SyntaxKind>,
        tokens: Vec<(SyntaxKind, Range<usize>, String)>,
        before: ParseLocalValueSnapshot,
        after: ParseLocalValueSnapshot,
        sink_clean: bool,
        cut: bool,
    }

    fn item_is_complete(item: &Recovered<DeclarationCompanionItem<'_>>) -> bool {
        matches!(
            item,
            Recovered::Complete(DeclarationCompanionItem::Statement(_))
        )
    }

    fn enter_test_braced_owner_scope(local: &mut ParseLocal) {
        local.set_inline(true);
        local.set_ml_arg(true);
        local.push_delimiter(Delimiter::Brace);
        local.push_stop_set(
            StopSet::default()
                .with(StopKind::Comma)
                .with(StopKind::Semicolon)
                .with(StopKind::RightBrace),
        );
    }

    fn seed_test_local(local: &mut ParseLocal) {
        local.set_line(LineState {
            at_line_start: false,
            ..LineState::default()
        });
        local.set_inline(true);
        local.set_ml_arg(true);
        local.set_type_ml_arg(true);
        local.push_indentation_baseline(IndentationBaseline {
            column: 0,
            kind: IndentationBaselineKind::Block,
        });
        local.push_indentation_baseline(IndentationBaseline {
            column: 0,
            kind: IndentationBaselineKind::Introducer,
        });
        local.push_type_expression_episode(TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops: StopSet::default().with(StopKind::With),
            fresh_primary_owns_adjacent_polymorphic_variant_starter: false,
        });
        local.push_type_expression_episode(TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops: StopSet::default().with(StopKind::Via),
            fresh_primary_owns_adjacent_polymorphic_variant_starter: true,
        });
        local.push_type_expression_scoped_stop_frame(TypeExpressionScopedStopFrame {
            stops: StopSet::default().with(StopKind::With),
            visible_episode_depth: 1,
        });
        local.push_type_expression_scoped_stop_frame(TypeExpressionScopedStopFrame {
            stops: StopSet::default().with(StopKind::Via),
            visible_episode_depth: 2,
        });
        local.push_stop_set(StopSet::default().with(StopKind::With));
        local.push_stop_set(StopSet::default().with(StopKind::RightBracket));
        local.push_delimiter(Delimiter::Brace);
        local.push_delimiter(Delimiter::Parenthesis);
        local.push_expression_delimited_owner(ExpressionDelimitedOwner::Call);
        local.push_expression_delimited_owner(ExpressionDelimitedOwner::Index);
        local.push_type_delimited_owner(TypeDelimitedOwner::Call);
        local.push_type_delimited_owner(TypeDelimitedOwner::NamedRecord);
        local.push_lexical_mode(EmbeddedLexicalMode::RuleLiteral);
        local.push_lexical_mode(EmbeddedLexicalMode::NormalString);
        local.push_root_statement_ambient_scope();
        local.push_inline_canonical_statement_ambient_scope(InlineStatementOwnerKind::WithBodyTail);
        local.push_if_expression_companion(37, &["__gate2_outer"]);
        local.push_if_expression_companion(41, &["__gate2_inner"]);
        local.stage_header_fact(StagedHeaderFact::Import);
        local.stage_header_fact(StagedHeaderFact::Operator);
        local.begin_operator_probe(OperatorCandidateProbe {
            start: 11,
            candidate_end: 17,
        });
        local.begin_operator_probe(OperatorCandidateProbe {
            start: 23,
            candidate_end: 29,
        });
        let _ = local.next_diagnostic_id();
        let _ = local.next_diagnostic_id();
        local.set_type_malformed_caller_boundary(Some(TypeMalformedCallerBoundaryFence {
            trivia_start: 31,
        }));
    }

    fn seeded_test_local() -> ParseLocal {
        let mut identity_owner = ParseLocal::new();
        let role = declaration_companion_item_role();
        let range = 97..97;
        let reusable = CommittedRecoveryRecord::new(
            &mut identity_owner,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Statement,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        );
        let mut local = ParseLocal::with_reusable_recoveries(&[reusable]);
        seed_test_local(&mut local);
        local
    }

    fn run_indented_ast(source: &str, block_indent: usize) -> AstOutcome {
        let table = OperatorTable::empty();
        run_indented_ast_with_table(source, block_indent, &table)
    }

    fn run_indented_ast_with_table(
        source: &str,
        block_indent: usize,
        table: &OperatorTable,
    ) -> AstOutcome {
        let mut input = SourceInput::new(source);
        let mut local = seeded_test_local();
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let items =
            parse_indented_declaration_companion_statement_items(table, block_indent, &mut i);
        let remainder = i.input.remainder().to_owned();
        drop(i);
        AstOutcome {
            complete: items.iter().map(item_is_complete).collect(),
            remainder,
            before,
            after: local.value_snapshot(),
            sink_clean: sink.take_merged().is_none(),
            cut,
        }
    }

    fn run_braced_ast(source: &str) -> AstOutcome {
        let table = OperatorTable::empty();
        run_braced_ast_with_table(source, &table)
    }

    fn run_braced_ast_with_table(source: &str, table: &OperatorTable) -> AstOutcome {
        let mut input = SourceInput::new(source);
        let mut local = seeded_test_local();
        enter_test_braced_owner_scope(&mut local);
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let items = parse_braced_declaration_companion_statement_items(table, &mut i);
        let remainder = i.input.remainder().to_owned();
        drop(i);
        AstOutcome {
            complete: items.iter().map(item_is_complete).collect(),
            remainder,
            before,
            after: local.value_snapshot(),
            sink_clean: sink.take_merged().is_none(),
            cut,
        }
    }

    fn run_indented_direct(source: &str, block_indent: usize) -> DirectOutcome {
        let table = OperatorTable::empty();
        run_indented_direct_with_table(source, block_indent, &table)
    }

    fn run_indented_direct_with_table(
        source: &str,
        block_indent: usize,
        table: &OperatorTable,
    ) -> DirectOutcome {
        let mut input = SourceInput::new(source);
        let mut local = seeded_test_local();
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let probe = Probe::new(i);
        let mut committed = probe.commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_indented_declaration_companion_statement_items(table, block_indent, &mut committed);
        let remainder = committed.probe(|probe| probe.input().input.remainder().to_owned());
        committed.finish_node();
        let output = committed.into_output();
        let recoveries = output.committed_recoveries().to_vec();
        let root = SyntaxNode::new_root(output.finish_prefix());
        let child_kinds = root.children().map(|node| node.kind()).collect();
        let node_kinds = root.descendants().map(|node| node.kind()).collect();
        let tokens = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| {
                let range = token.text_range();
                (
                    token.kind(),
                    usize::from(range.start())..usize::from(range.end()),
                    token.text().to_owned(),
                )
            })
            .collect();
        DirectOutcome {
            statement_count: root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Statement)
                .count(),
            remainder,
            recoveries,
            emitted: root.to_string(),
            child_kinds,
            node_kinds,
            tokens,
            before,
            after: local.value_snapshot(),
            sink_clean: sink.take_merged().is_none(),
            cut,
        }
    }

    fn run_braced_direct(source: &str) -> DirectOutcome {
        let table = OperatorTable::empty();
        run_braced_direct_with_table(source, &table)
    }

    fn run_braced_direct_with_table(source: &str, table: &OperatorTable) -> DirectOutcome {
        let mut input = SourceInput::new(source);
        let mut local = seeded_test_local();
        enter_test_braced_owner_scope(&mut local);
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let probe = Probe::new(i);
        let mut committed = probe.commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_braced_declaration_companion_statement_items(table, &mut committed);
        let remainder = committed.probe(|probe| probe.input().input.remainder().to_owned());
        committed.finish_node();
        let output = committed.into_output();
        let recoveries = output.committed_recoveries().to_vec();
        let root = SyntaxNode::new_root(output.finish_prefix());
        let child_kinds = root.children().map(|node| node.kind()).collect();
        let node_kinds = root.descendants().map(|node| node.kind()).collect();
        let tokens = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| {
                let range = token.text_range();
                (
                    token.kind(),
                    usize::from(range.start())..usize::from(range.end()),
                    token.text().to_owned(),
                )
            })
            .collect();
        DirectOutcome {
            statement_count: root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Statement)
                .count(),
            remainder,
            recoveries,
            emitted: root.to_string(),
            child_kinds,
            node_kinds,
            tokens,
            before,
            after: local.value_snapshot(),
            sink_clean: sink.take_merged().is_none(),
            cut,
        }
    }

    fn expected_line_after_prefix(mut line: LineState, prefix: &str) -> LineState {
        let bytes = prefix.as_bytes();
        let mut index = 0;
        while index < bytes.len() {
            let start = index;
            let newline_end = if bytes[index] == b'\r' {
                index + 1 + usize::from(bytes.get(index + 1) == Some(&b'\n'))
            } else if bytes[index] == b'\n' {
                index + 1
            } else {
                0
            };
            if newline_end != 0 {
                line = LineState {
                    last_newline: Some((start, newline_end)),
                    line_start: newline_end,
                    line_indent: 0,
                    at_line_start: true,
                };
                index = newline_end;
                continue;
            }
            if matches!(bytes[index], b' ' | b'\t') && line.at_line_start {
                line.line_indent += 1;
            } else if !matches!(bytes[index], b' ' | b'\t') {
                line.at_line_start = false;
            }
            index += 1;
        }
        line
    }

    fn unterminated_block_comment_depth(prefix: &str) -> usize {
        let bytes = prefix.as_bytes();
        let mut index = 0;
        let mut depth = 0;
        while index + 1 < bytes.len() {
            if depth == 0 && bytes[index..].starts_with(b"//") {
                index += 2;
                while index < bytes.len() && !matches!(bytes[index], b'\r' | b'\n') {
                    index += 1;
                }
                continue;
            }
            if bytes[index..].starts_with(b"/*") {
                depth += 1;
                index += 2;
                continue;
            }
            if depth > 0 && bytes[index..].starts_with(b"*/") {
                depth -= 1;
                index += 2;
                continue;
            }
            index += 1;
        }
        depth
    }

    fn expected_local_after(
        before: &ParseLocalValueSnapshot,
        source: &str,
        remainder: &str,
        diagnostic_delta: u32,
        next_if_expression_companion_id_delta: u32,
    ) -> ParseLocalValueSnapshot {
        let consumed_end = source.len() - remainder.len();
        let prefix = &source[..consumed_end];
        let mut expected = before.clone();
        expected.line = expected_line_after_prefix(before.line, prefix);
        let unterminated_depth = unterminated_block_comment_depth(prefix);
        if unterminated_depth > 0 {
            expected
                .lexical_modes
                .push(EmbeddedLexicalMode::BlockComment {
                    depth: unterminated_depth,
                });
        }
        expected.next_diagnostic_id += diagnostic_delta;
        expected.next_if_expression_companion_id += next_if_expression_companion_id_delta;
        expected
    }

    fn assert_full_local_parity_with_semantic_delta(
        source: &str,
        ast: &AstOutcome,
        direct: &DirectOutcome,
        next_if_expression_companion_id_delta: u32,
    ) {
        let expected_ast_after = expected_local_after(
            &ast.before,
            source,
            &ast.remainder,
            0,
            next_if_expression_companion_id_delta,
        );
        assert_eq!(
            expected_ast_after, ast.after,
            "AST full local state: {source:?}"
        );
        let expected_direct_after = expected_local_after(
            &direct.before,
            source,
            &direct.remainder,
            direct.recoveries.len() as u32,
            next_if_expression_companion_id_delta,
        );
        assert_eq!(
            expected_direct_after, direct.after,
            "direct full local state: {source:?}"
        );
        assert_full_local_ast_direct_after_parity(source, ast, direct);
    }

    fn assert_full_local_ast_direct_after_parity(
        source: &str,
        ast: &AstOutcome,
        direct: &DirectOutcome,
    ) {
        let mut normalized_direct_after = direct.after.clone();
        normalized_direct_after.next_diagnostic_id = ast.after.next_diagnostic_id;
        assert_eq!(
            ast.after, normalized_direct_after,
            "AST/direct full local parity: {source:?}"
        );
    }

    fn assert_common_parity(source: &str, ast: &AstOutcome, direct: &DirectOutcome) {
        assert_common_parity_with_cut(source, ast, direct, false, false);
    }

    fn assert_common_parity_with_cut(
        source: &str,
        ast: &AstOutcome,
        direct: &DirectOutcome,
        expected_ast_cut: bool,
        expected_direct_cut: bool,
    ) {
        assert_common_parity_with_cut_and_semantic_delta(
            source,
            ast,
            direct,
            expected_ast_cut,
            expected_direct_cut,
            0,
        );
    }

    fn assert_common_parity_with_cut_and_semantic_delta(
        source: &str,
        ast: &AstOutcome,
        direct: &DirectOutcome,
        expected_ast_cut: bool,
        expected_direct_cut: bool,
        next_if_expression_companion_id_delta: u32,
    ) {
        assert_eq!(
            ast.complete.len(),
            direct.statement_count,
            "items: {source:?}"
        );
        assert_eq!(ast.remainder, direct.remainder, "remainder: {source:?}");
        assert_eq!(
            format!("{}{}", direct.emitted, direct.remainder),
            source,
            "parser prefix plus retained remainder: {source:?}"
        );
        assert_full_local_parity_with_semantic_delta(
            source,
            ast,
            direct,
            next_if_expression_companion_id_delta,
        );
        assert!(ast.sink_clean, "AST sink: {source:?}");
        assert!(direct.sink_clean, "direct sink: {source:?}");
        assert_eq!(ast.cut, expected_ast_cut, "AST cut: {source:?}");
        assert_eq!(direct.cut, expected_direct_cut, "direct cut: {source:?}");
        for (index, record) in direct.recoveries.iter().enumerate() {
            let expected = if record.site.role == declaration_companion_separator_role() {
                ExpectedSyntax::StatementSeparator
            } else {
                assert!(
                    record.site.role == declaration_companion_item_role()
                        || record.site.role == declaration_companion_indented_item_role(),
                    "unexpected Gate 2 companion recovery role: {source:?}"
                );
                ExpectedSyntax::Statement
            };
            assert_eq!(
                record.id.0,
                direct.before.next_diagnostic_id + index as u32,
                "recovery source order: {source:?}"
            );
            match record.kind {
                RecoveryKind::Missing => {
                    assert!(
                        record.unexpected.is_empty(),
                        "missing unexpected: {source:?}"
                    )
                }
                RecoveryKind::Error => assert_eq!(
                    record.unexpected.as_ref(),
                    [UnexpectedSyntax::Token {
                        range: record.site.range.clone(),
                        category: UnexpectedCategory::OtherCharacter,
                    }],
                    "error unexpected order: {source:?}"
                ),
            }
            assert_eq!(
                record.expectations.as_ref(),
                [SyntaxExpectation {
                    role: record.site.role,
                    expected,
                    range: record.site.range.clone(),
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }],
                "expectation/source order: {source:?}"
            );
            assert_eq!(
                record.primary_expectation, 0,
                "primary expectation: {source:?}"
            );
        }
    }

    fn recovery_summary(
        records: &[CommittedRecoveryRecord],
    ) -> Vec<(RecoveryKind, GrammarRole, Range<usize>)> {
        records
            .iter()
            .map(|record| (record.kind, record.site.role, record.site.range.clone()))
            .collect()
    }

    fn gate2_indented_statement_only_companion_recovery_and_boundaries_match() {
        let indented_item = declaration_companion_indented_item_role();
        for (source, block_indent, complete, remainder, recoveries) in [
            ("first\nsecond", 0, vec![true, true], "", vec![]),
            (
                "@ first\nsecond",
                0,
                vec![true, true],
                "",
                vec![(RecoveryKind::Error, indented_item, 0..2)],
            ),
            (
                "@ \nsecond",
                0,
                vec![false, true],
                "",
                vec![(RecoveryKind::Error, indented_item, 0..2)],
            ),
            (
                ";first",
                0,
                vec![false, true],
                "",
                vec![(RecoveryKind::Missing, indented_item, 0..0)],
            ),
            ("first;\nouter", 2, vec![true], "\nouter", vec![]),
            ("first\nouter", 2, vec![true], "\nouter", vec![]),
            (
                ")outer",
                0,
                vec![false],
                ")outer",
                vec![(RecoveryKind::Missing, indented_item, 0..0)],
            ),
        ] {
            let ast = run_indented_ast(source, block_indent);
            let direct = run_indented_direct(source, block_indent);
            assert_common_parity(source, &ast, &direct);
            assert_eq!(ast.complete, complete, "complete items: {source:?}");
            assert_eq!(ast.remainder, remainder, "boundary: {source:?}");
            assert_eq!(
                recovery_summary(&direct.recoveries),
                recoveries,
                "recoveries: {source:?}"
            );
        }
    }

    fn gate2_braced_statement_only_companion_recovery_and_transitions_match() {
        let item = declaration_companion_item_role();
        let separator = declaration_companion_separator_role();
        for (source, complete, remainder, recoveries) in [
            ("", vec![], "", vec![]),
            ("}outer", vec![], "}outer", vec![]),
            (")outer", vec![], ")outer", vec![]),
            ("]outer", vec![], "]outer", vec![]),
            (" \t)outer", vec![], " \t)outer", vec![]),
            ("first,second", vec![true, true], "", vec![]),
            (
                ",first",
                vec![false, true],
                "",
                vec![(RecoveryKind::Missing, item, 0..0)],
            ),
            (
                "first,,second",
                vec![true, false, true],
                "",
                vec![(RecoveryKind::Missing, item, 6..6)],
            ),
            ("first,}", vec![true], "}", vec![]),
            ("first,)", vec![true], ")", vec![]),
            ("first,]", vec![true], "]", vec![]),
            ("first)", vec![true], ")", vec![]),
            ("first]", vec![true], "]", vec![]),
            (
                "@ first}",
                vec![true],
                "}",
                vec![(RecoveryKind::Error, item, 0..2)],
            ),
            (
                "@}",
                vec![false],
                "}",
                vec![(RecoveryKind::Error, item, 0..1)],
            ),
            (
                "first second}",
                vec![true, true],
                "}",
                vec![(RecoveryKind::Missing, separator, 6..6)],
            ),
            ("first\nsecond}", vec![true, true], "}", vec![]),
        ] {
            let ast = run_braced_ast(source);
            let direct = run_braced_direct(source);
            assert_common_parity(source, &ast, &direct);
            assert_eq!(ast.complete, complete, "complete items: {source:?}");
            assert_eq!(ast.remainder, remainder, "boundary: {source:?}");
            assert_eq!(
                recovery_summary(&direct.recoveries),
                recoveries,
                "recoveries: {source:?}"
            );
        }
        for source in [")outer", "]outer", " \t)outer"] {
            let direct = run_braced_direct(source);
            assert_eq!(direct.child_kinds, Vec::<SyntaxKind>::new(), "{source:?}");
            assert_eq!(direct.node_kinds, vec![SyntaxKind::Root], "{source:?}");
            assert!(direct.tokens.is_empty(), "{source:?}");
            assert!(direct.recoveries.is_empty(), "{source:?}");
            assert_eq!(direct.emitted, "", "{source:?}");
            assert_eq!(direct.remainder, source, "{source:?}");
        }
    }

    fn gate2_statement_only_companion_keeps_ast_direct_cardinality_and_stack_state() {
        for source in ["first", "@ first", "@", ";first", "first;second"] {
            let ast = run_indented_ast(source, 0);
            let direct = run_indented_direct(source, 0);
            assert_common_parity(source, &ast, &direct);
        }
        for source in ["", "first", "@ first", "@", ",first", "first,second"] {
            let ast = run_braced_ast(source);
            let direct = run_braced_direct(source);
            assert_common_parity(source, &ast, &direct);
        }
    }

    fn assert_statement_recovery(
        record: &CommittedRecoveryRecord,
        kind: RecoveryKind,
        role: GrammarRole,
        range: Range<usize>,
    ) {
        assert_eq!(record.kind, kind);
        assert_eq!(record.site.role, role);
        assert_eq!(record.site.range, range);
        match kind {
            RecoveryKind::Missing => assert!(record.unexpected.is_empty()),
            RecoveryKind::Error => assert_eq!(
                record.unexpected.as_ref(),
                [UnexpectedSyntax::Token {
                    range: range.clone(),
                    category: UnexpectedCategory::OtherCharacter,
                }]
            ),
        }
        assert_eq!(
            record.expectations.as_ref(),
            [SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Statement,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]
        );
        assert_eq!(record.primary_expectation, 0);
    }

    fn gate2_comment_aware_recovery_is_atomic_and_ast_direct_exact() {
        let item = declaration_companion_item_role();
        for (source, complete, error_end, remainder) in [
            (
                "@ /* } first,;)] inside */ value}",
                vec![true],
                "@ /* } first,;)] inside */ ".len(),
                "}",
            ),
            (
                "@ /* outer /* first,;)]} */ end */ value}",
                vec![true],
                "@ /* outer /* first,;)]} */ end */ ".len(),
                "}",
            ),
            (
                "@ // first,;)]} inside\nvalue}",
                vec![false, true],
                "@ // first,;)]} inside".len(),
                "}",
            ),
            (
                "@ /* unterminated first,;)]}",
                vec![false],
                "@ /* unterminated first,;)]}".len(),
                "",
            ),
        ] {
            let ast = run_braced_ast(source);
            let direct = run_braced_direct(source);
            assert_common_parity(source, &ast, &direct);
            assert_eq!(ast.complete, complete, "{source:?}");
            assert_eq!(ast.remainder, remainder, "{source:?}");
            assert_eq!(direct.recoveries.len(), 1, "{source:?}");
            assert_statement_recovery(
                &direct.recoveries[0],
                RecoveryKind::Error,
                item,
                0..error_end,
            );
            assert_eq!(
                direct.recoveries[0].id.0, direct.before.next_diagnostic_id,
                "{source:?}"
            );
            let mut expected_lexical_modes = ast.before.lexical_modes.clone();
            if source.contains("unterminated") {
                expected_lexical_modes.push(EmbeddedLexicalMode::BlockComment { depth: 1 });
            }
            assert_eq!(
                ast.after.lexical_modes, expected_lexical_modes,
                "lexical mode exit: {source:?}"
            );
            assert_eq!(direct.tokens.first().map(|token| token.1.start), Some(0));
            assert_eq!(
                direct.tokens.last().map(|token| token.1.end),
                Some(source.len() - remainder.len())
            );
            assert_eq!(
                direct
                    .tokens
                    .windows(2)
                    .map(|pair| (pair[0].1.end, pair[1].1.start))
                    .collect::<Vec<_>>(),
                direct
                    .tokens
                    .windows(2)
                    .map(|pair| (pair[0].1.end, pair[0].1.end))
                    .collect::<Vec<_>>(),
                "contiguous token ranges: {source:?}"
            );
            assert_eq!(
                direct
                    .tokens
                    .iter()
                    .map(|token| token.2.as_str())
                    .collect::<String>(),
                &source[..source.len() - remainder.len()],
                "token text order: {source:?}"
            );
            let expected_tokens = if source.contains("unterminated") {
                vec![(SyntaxKind::Unknown, 0..source.len(), source.to_owned())]
            } else if complete.len() == 2 {
                vec![
                    (
                        SyntaxKind::Unknown,
                        0..error_end,
                        source[..error_end].to_owned(),
                    ),
                    (
                        SyntaxKind::Newline,
                        error_end..error_end + 1,
                        "\n".to_owned(),
                    ),
                    (
                        SyntaxKind::Identifier,
                        error_end + 1..source.len() - 1,
                        "value".to_owned(),
                    ),
                ]
            } else {
                vec![
                    (
                        SyntaxKind::Unknown,
                        0..error_end,
                        source[..error_end].to_owned(),
                    ),
                    (
                        SyntaxKind::Identifier,
                        error_end..source.len() - 1,
                        "value".to_owned(),
                    ),
                ]
            };
            assert_eq!(direct.tokens, expected_tokens, "exact tokens: {source:?}");
            assert_eq!(
                direct.child_kinds,
                if complete.len() == 2 {
                    vec![
                        SyntaxKind::Statement,
                        SyntaxKind::BlockStatementSeparator,
                        SyntaxKind::Statement,
                    ]
                } else {
                    vec![SyntaxKind::Statement]
                },
                "sequence shell nodes: {source:?}"
            );
            assert_eq!(
                direct.node_kinds,
                if complete.len() == 2 {
                    vec![
                        SyntaxKind::Root,
                        SyntaxKind::Statement,
                        SyntaxKind::Error,
                        SyntaxKind::BlockStatementSeparator,
                        SyntaxKind::Statement,
                        SyntaxKind::OperatorChain,
                        SyntaxKind::IdentifierExpression,
                    ]
                } else if source.contains("unterminated") {
                    vec![SyntaxKind::Root, SyntaxKind::Statement, SyntaxKind::Error]
                } else {
                    vec![
                        SyntaxKind::Root,
                        SyntaxKind::Statement,
                        SyntaxKind::Error,
                        SyntaxKind::OperatorChain,
                        SyntaxKind::IdentifierExpression,
                    ]
                },
                "exact sequence descendant nodes: {source:?}"
            );
        }
    }

    fn gate2_candidate_operator_table() -> OperatorTable {
        OperatorTable::from_declarations([
            OperatorDeclaration::new(
                "+",
                OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            ),
            OperatorDeclaration::new("!", OperatorFixities::new().with_nullfix()),
        ])
        .expect("Gate 2 candidate operators are non-conflicting")
    }

    fn gate2_comment_prefix_operator_table() -> OperatorTable {
        OperatorTable::from_declarations([OperatorDeclaration::new(
            "/",
            OperatorFixities::new()
                .with_prefix(BindingPower::scalar(70))
                .with_nullfix(),
        )])
        .expect("the comment-prefix regression operator is non-conflicting")
    }

    fn gate2_comment_openers_precede_slash_statement_candidates() {
        let table = gate2_comment_prefix_operator_table();
        for source in ["/", "/ value"] {
            let ast = run_indented_ast_with_table(source, 0, &table);
            let direct = run_indented_direct_with_table(source, 0, &table);
            assert_common_parity_with_cut(source, &ast, &direct, false, source != "/");
            assert_eq!(
                ast.complete,
                vec![true],
                "normal slash Statement: {source:?}"
            );
            assert!(direct.recoveries.is_empty(), "{source:?}");
        }

        let non_comment = "@ / value}";
        let ast = run_braced_ast_with_table(non_comment, &table);
        let direct = run_braced_direct_with_table(non_comment, &table);
        assert_common_parity_with_cut(non_comment, &ast, &direct, false, true);
        assert_eq!(ast.complete, vec![true]);
        assert_eq!(ast.remainder, "}");
        assert_eq!(
            recovery_summary(&direct.recoveries),
            vec![(RecoveryKind::Error, declaration_companion_item_role(), 0..2,)]
        );
        assert!(
            direct.node_kinds.contains(&SyntaxKind::PrefixOperatorUse),
            "the non-comment slash remains the retried Statement candidate"
        );

        for (source, complete, error_end) in [
            (
                "@ /* / internal value; ) ] } , */ value}",
                vec![true],
                "@ /* / internal value; ) ] } , */ ".len(),
            ),
            (
                "@ // / internal value; ) ] } ,\nvalue}",
                vec![false, true],
                "@ // / internal value; ) ] } ,".len(),
            ),
        ] {
            let ast = run_braced_ast_with_table(source, &table);
            let direct = run_braced_direct_with_table(source, &table);
            assert_common_parity(source, &ast, &direct);
            assert_eq!(ast.complete, complete, "{source:?}");
            assert_eq!(ast.remainder, "}", "{source:?}");
            assert_eq!(
                recovery_summary(&direct.recoveries),
                vec![(
                    RecoveryKind::Error,
                    declaration_companion_item_role(),
                    0..error_end,
                )]
            );
            assert!(
                !direct.node_kinds.iter().any(|kind| matches!(
                    kind,
                    SyntaxKind::PrefixOperatorUse | SyntaxKind::NullfixOperatorUse
                )),
                "a slash inside the comment cannot become a retry: {source:?}"
            );
        }
    }

    fn gate2_if_retry_allocates_one_identity_only_after_candidate_probe() {
        let table = OperatorTable::empty();
        let source = "@ if value: value}";

        let mut input = SourceInput::new(source);
        let mut local = seeded_test_local();
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        assert_eq!(
            canonical_statement_invalid_run(&table, &mut i),
            Some((0..2, true))
        );
        let remainder = i.input.remainder().to_owned();
        drop(i);
        assert_eq!(remainder, "if value: value}");
        assert_eq!(
            local.value_snapshot(),
            expected_local_after(&before, source, &remainder, 0, 0),
            "the candidate probe must not allocate an If companion identity"
        );
        assert!(sink.take_merged().is_none());
        assert!(!cut);

        let ast = run_braced_ast(source);
        let direct = run_braced_direct(source);
        assert_common_parity_with_cut_and_semantic_delta(source, &ast, &direct, true, true, 1);
        assert_eq!(ast.complete, vec![true]);
        assert_eq!(ast.remainder, "}");
        assert_eq!(
            recovery_summary(&direct.recoveries),
            vec![(RecoveryKind::Error, declaration_companion_item_role(), 0..2)]
        );
        assert_eq!(
            direct
                .node_kinds
                .iter()
                .filter(|kind| **kind == SyntaxKind::IfExpression)
                .count(),
            1
        );
    }

    fn gate2_every_canonical_statement_candidate_family_has_ast_direct_parity() {
        let table = gate2_candidate_operator_table();
        for (family, source) in [
            ("binding declaration", "my value = 1"),
            ("use declaration", "use std::io"),
            ("mod declaration", "mod outer;"),
            ("struct declaration", "struct Marker;"),
            ("enum declaration", "enum Choice { One }"),
            ("error declaration", "error Failure { One }"),
            ("type declaration", "type Value = Int"),
            ("role declaration", "role Eq;"),
            ("impl declaration", "impl Int;"),
            ("cast declaration", "cast(value: A): Int"),
            ("act declaration", "act Console::Read;"),
            ("for statement", "for value in values: value"),
            ("parenthesized NUD", "()"),
            ("braced-block NUD", "{}"),
            ("if NUD", "if value: value"),
            ("case NUD", "case value: item -> value"),
            ("catch NUD", "catch value: item -> value"),
            ("identifier NUD", "value"),
            ("integer NUD", "1"),
            ("prefix NUD", "+value"),
            ("nullfix NUD", "!"),
        ] {
            let ast = run_indented_ast_with_table(source, 0, &table);
            let direct = run_indented_direct_with_table(source, 0, &table);
            assert_eq!(ast.complete.len(), direct.statement_count, "{family}");
            assert_eq!(ast.remainder, direct.remainder, "{family}");
            assert_eq!(
                format!("{}{}", direct.emitted, direct.remainder),
                source,
                "{family}"
            );
            assert_full_local_parity_with_semantic_delta(
                source,
                &ast,
                &direct,
                u32::from(family == "if NUD"),
            );
            assert_eq!(ast.complete, vec![true], "{family}: {source:?}");
            assert_eq!(ast.remainder, "", "{family}: {source:?}");

            let braced_source = format!("{source}}}");
            let ast = run_braced_ast_with_table(&braced_source, &table);
            let direct = run_braced_direct_with_table(&braced_source, &table);
            assert_eq!(
                ast.complete.len(),
                direct.statement_count,
                "braced {family}"
            );
            assert_eq!(ast.remainder, direct.remainder, "braced {family}");
            assert_eq!(
                format!("{}{}", direct.emitted, direct.remainder),
                braced_source,
                "braced {family}"
            );
            assert_full_local_parity_with_semantic_delta(
                &braced_source,
                &ast,
                &direct,
                u32::from(family == "if NUD"),
            );
            assert_eq!(ast.complete, vec![true], "braced {family}: {source:?}");
            assert_eq!(ast.remainder, "}", "braced {family}: {source:?}");
        }
    }

    fn gate2_valid_large_sequences_never_call_the_recovery_candidate_helper() {
        let table = OperatorTable::empty();
        assert_eq!(synthetic_indented_source(0), "");
        assert_eq!(synthetic_indented_source(3), "item\nitem\nitem");
        assert_eq!(synthetic_braced_source(3), "item,item,item");
        for item_count in [1_000, 10_000] {
            let indented = synthetic_indented_source(item_count);
            reset_canonical_statement_candidate_input_calls();
            let (items, remainder) = timed_indented_ast(&table, &indented);
            assert_eq!(items.len(), item_count);
            assert_eq!(remainder, 0);
            assert_eq!(canonical_statement_candidate_input_calls(), 0);

            reset_canonical_statement_candidate_input_calls();
            let (output, remainder) = timed_indented_direct(&table, &indented);
            assert_eq!(remainder, 0);
            assert_eq!(canonical_statement_candidate_input_calls(), 0);
            black_box(output);

            let braced = synthetic_braced_source(item_count);
            reset_canonical_statement_candidate_input_calls();
            let (items, remainder) = timed_braced_ast(&table, &braced);
            assert_eq!(items.len(), item_count);
            assert_eq!(remainder, 0);
            assert_eq!(canonical_statement_candidate_input_calls(), 0);

            reset_canonical_statement_candidate_input_calls();
            let (output, remainder) = timed_braced_direct(&table, &braced);
            assert_eq!(remainder, 0);
            assert_eq!(canonical_statement_candidate_input_calls(), 0);
            black_box(output);
        }
    }

    fn synthetic_repeated_source(items: usize, item: &str, separator: char) -> String {
        let capacity = item
            .len()
            .checked_mul(items)
            .and_then(|bytes| {
                separator
                    .len_utf8()
                    .checked_mul(items.saturating_sub(1))
                    .and_then(|separator_bytes| bytes.checked_add(separator_bytes))
            })
            .expect("synthetic Gate 2 source length fits usize");
        let mut source = String::with_capacity(capacity);
        for index in 0..items {
            if index > 0 {
                source.push(separator);
            }
            source.push_str(item);
        }
        assert_eq!(source.len(), capacity);
        source
    }

    fn synthetic_indented_source(items: usize) -> String {
        synthetic_repeated_source(items, "item", '\n')
    }

    fn synthetic_braced_source(items: usize) -> String {
        synthetic_repeated_source(items, "item", ',')
    }

    fn timed_indented_ast<'source>(
        table: &OperatorTable,
        source: &'source str,
    ) -> (Vec<Recovered<DeclarationCompanionItem<'source>>>, usize) {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let parsed = parse_indented_declaration_companion_statement_items(table, 0, &mut i);
        let remainder = i.input.remainder().len();
        (parsed, remainder)
    }

    fn timed_braced_ast<'source>(
        table: &OperatorTable,
        source: &'source str,
    ) -> (Vec<Recovered<DeclarationCompanionItem<'source>>>, usize) {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        enter_test_braced_owner_scope(&mut local);
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let parsed = parse_braced_declaration_companion_statement_items(table, &mut i);
        let remainder = i.input.remainder().len();
        (parsed, remainder)
    }

    fn timed_indented_direct<'source>(
        table: &OperatorTable,
        source: &'source str,
    ) -> (FullCstOutput<'source>, usize) {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let probe = Probe::new(i);
        let mut committed = probe.commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_indented_declaration_companion_statement_items(table, 0, &mut committed);
        let remainder = committed.probe(|probe| probe.input().input.remainder().len());
        committed.finish_node();
        let output = committed.into_output();
        (output, remainder)
    }

    fn timed_braced_direct<'source>(
        table: &OperatorTable,
        source: &'source str,
    ) -> (FullCstOutput<'source>, usize) {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        enter_test_braced_owner_scope(&mut local);
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let probe = Probe::new(i);
        let mut committed = probe.commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_braced_declaration_companion_statement_items(table, &mut committed);
        let remainder = committed.probe(|probe| probe.input().input.remainder().len());
        committed.finish_node();
        let output = committed.into_output();
        (output, remainder)
    }

    #[test]
    fn gate2_companion_sequence_table() {
        gate2_indented_statement_only_companion_recovery_and_boundaries_match();
        gate2_braced_statement_only_companion_recovery_and_transitions_match();
        gate2_statement_only_companion_keeps_ast_direct_cardinality_and_stack_state();
        gate2_comment_aware_recovery_is_atomic_and_ast_direct_exact();
        gate2_comment_openers_precede_slash_statement_candidates();
        gate2_if_retry_allocates_one_identity_only_after_candidate_probe();
        gate2_every_canonical_statement_candidate_family_has_ast_direct_parity();
        gate2_valid_large_sequences_never_call_the_recovery_candidate_helper();
    }
}

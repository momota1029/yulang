use super::*;

use std::{
    ops::Range,
    panic::{AssertUnwindSafe, catch_unwind},
    sync::Arc,
};

use crate::rewrite::yumark::{FenceOpener, FencePrefixPolicy};
use crate::session::{
    ConstructRole, Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
    PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation, TypeRole,
    UnexpectedCategory, UnexpectedSyntax,
};
use chasa_recover::Recoverable as _;

mod pe_recovery;
mod pv_recovery;

fn top_type_expression(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeExpression)
        .expect("top-level type expression")
}

fn expected_type_error(id: u32, role: TypeRole, range: Range<usize>) -> CommittedRecoveryRecord {
    let role = GrammarRole::Type(role);
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: RecoveryKind::Error,
        unexpected: Arc::from([UnexpectedSyntax::Token {
            range: range.clone(),
            category: UnexpectedCategory::OtherCharacter,
        }]),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Identifier,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn expected_parenthesized_close(id: u32, at: usize) -> CommittedRecoveryRecord {
    let role = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::ParenthesizedTypeGroup,
        delimiter: Delimiter::Parenthesis,
    };
    let range = at..at;
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: RecoveryKind::Missing,
        unexpected: Arc::from([]),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Close(
                Delimiter::Parenthesis,
            )),
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn expected_type_call_close(id: u32, at: usize) -> CommittedRecoveryRecord {
    let role = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::TypeCall,
        delimiter: Delimiter::Parenthesis,
    };
    let range = at..at;
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: RecoveryKind::Missing,
        unexpected: Arc::from([]),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Close(
                Delimiter::Parenthesis,
            )),
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn expected_type_call_close_error(id: u32, range: Range<usize>) -> CommittedRecoveryRecord {
    let role = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::TypeCall,
        delimiter: Delimiter::Parenthesis,
    };
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: RecoveryKind::Error,
        unexpected: Arc::from([UnexpectedSyntax::Token {
            range: range.clone(),
            category: UnexpectedCategory::OtherCharacter,
        }]),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Close(
                Delimiter::Parenthesis,
            )),
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn expected_type_call_argument_error(id: u32, range: Range<usize>) -> CommittedRecoveryRecord {
    expected_type_expression_error(
        id,
        TypeRole::CallArgument,
        range.clone(),
        Arc::from([UnexpectedSyntax::Token {
            range,
            category: UnexpectedCategory::OtherCharacter,
        }]),
    )
}

fn expected_type_call_separator(id: u32, at: usize) -> CommittedRecoveryRecord {
    let role = GrammarRole::Type(TypeRole::CallArgumentSeparator);
    let range = at..at;
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: RecoveryKind::Missing,
        unexpected: Arc::from([]),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::DelimitedSequenceSeparator,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn expected_parenthesized_separator(id: u32, at: usize) -> CommittedRecoveryRecord {
    let role = GrammarRole::Type(TypeRole::ParenthesizedSeparator);
    let range = at..at;
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: RecoveryKind::Missing,
        unexpected: Arc::from([]),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::DelimitedSequenceSeparator,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn frozen_recovery_ids(records: &[CommittedRecoveryRecord]) -> Vec<CommittedRecoveryRecord> {
    records
        .iter()
        .enumerate()
        .map(|(index, record)| {
            let mut record = record.clone();
            record.id = DiagnosticId(7 + u32::try_from(index).expect("bounded recovery fixture"));
            record
        })
        .collect()
}

fn expected_required_type_primary_error(
    id: u32,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> CommittedRecoveryRecord {
    expected_type_expression_error(id, TypeRole::Primary, range, unexpected)
}

fn expected_type_expression_error(
    id: u32,
    role: TypeRole,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> CommittedRecoveryRecord {
    let role = GrammarRole::Type(role);
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: RecoveryKind::Error,
        unexpected,
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::TypeExpression,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn expected_type_expression_missing(id: u32, role: TypeRole, at: usize) -> CommittedRecoveryRecord {
    let role = GrammarRole::Type(role);
    let range = at..at;
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: RecoveryKind::Missing,
        unexpected: Arc::from([]),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::TypeExpression,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn expected_type_path_segment_recovery(
    id: u32,
    kind: RecoveryKind,
    range: Range<usize>,
) -> CommittedRecoveryRecord {
    let role = GrammarRole::Type(TypeRole::PathSegment);
    let unexpected = match kind {
        RecoveryKind::Missing => Arc::from([]),
        RecoveryKind::Error => Arc::from([UnexpectedSyntax::Token {
            range: range.clone(),
            category: UnexpectedCategory::OtherCharacter,
        }]),
    };
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::TypePathSegment,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn run_pattern_with_recoveries<'frozen>(
    source: &str,
    frozen: Option<&'frozen [CommittedRecoveryRecord]>,
) -> (GreenNode, TailExit, Vec<CommittedRecoveryRecord>) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut output = match frozen {
        Some(frozen) => GreenNodeBuilder::reconcile(frozen),
        None => GreenNodeBuilder::new(),
    };
    output.start_node(SyntaxKind::Root.into());
    let mut exit = pattern_with_stops(
        In::new(&mut input, &mut recover, &mut output),
        PATTERN_DEFAULT_STOPS,
    );
    if let Err(Either::Right(end)) = &mut exit {
        emit_end(&mut output, end);
    }
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    (green, exit, records)
}

fn run_required_type_with_recoveries<'source, 'frozen>(
    source: &'source str,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    frozen: Option<&'frozen [CommittedRecoveryRecord]>,
) -> (
    GreenNode,
    NormalizedExit,
    bool,
    &'source str,
    Vec<CommittedRecoveryRecord>,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut output = match frozen {
        Some(frozen) => GreenNodeBuilder::reconcile(frozen),
        None => GreenNodeBuilder::new(),
    };
    output.start_node(SyntaxKind::Root.into());
    let (primary, successor_origin, next_line_entry) =
        super::super::type_expr::type_nud_item_normalized(
            In::new(&mut input, &mut recover, &mut output),
            item_origin,
            line_entry,
            fence,
        );
    let (mut exit, primary_found) =
        super::super::type_expr::required_type_expr_with_caller_stops_and_completion_normalized(
            In::new(&mut input, &mut recover, &mut output),
            primary,
            0,
            0,
            successor_origin,
            next_line_entry,
            fence,
        );
    if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
        emit_end(&mut output, end);
    }
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    (green, exit, primary_found, input, records)
}

fn run_type_with_context_and_recoveries<'frozen>(
    source: &str,
    type_ml: super::super::type_expr::TypeMlContext,
    frozen: Option<&'frozen [CommittedRecoveryRecord]>,
) -> (GreenNode, NormalizedExit, Vec<CommittedRecoveryRecord>) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut output = match frozen {
        Some(frozen) => GreenNodeBuilder::reconcile(frozen),
        None => GreenNodeBuilder::new(),
    };
    output.start_node(SyntaxKind::Root.into());
    let (mut exit, _) = super::super::type_expr::type_expr_with_context_for_test(
        In::new(&mut input, &mut recover, &mut output),
        type_ml,
        0,
    )
    .expect("accepted contextual TypeExpression");
    if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
        emit_end(&mut output, end);
    }
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    (green, exit, records)
}

struct ContextualTypeRun<'source> {
    green: GreenNode,
    exit: NormalizedExit,
    successor_origin: usize,
    remainder: &'source str,
    records: Vec<CommittedRecoveryRecord>,
    slots: usize,
    diagnostics: (Option<u32>, usize),
    mark: (),
    same_operators: bool,
}

#[allow(clippy::too_many_arguments)]
fn run_contextual_type_snapshot<'source, 'frozen>(
    source: &'source str,
    type_ml: super::super::type_expr::TypeMlContext,
    caller_stops: Stops,
    outer_closes: u8,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    frozen: Option<&'frozen [CommittedRecoveryRecord]>,
) -> ContextualTypeRun<'source> {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mark = recover.mark();
    let same_operators = std::ptr::eq(recover.operators(), &operators);
    let mut output = match frozen {
        Some(frozen) => GreenNodeBuilder::reconcile(frozen),
        None => GreenNodeBuilder::new(),
    };
    output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut output);
    let (mut exit, successor_origin) =
        super::super::type_expr::type_expr_with_context_and_boundaries_for_test(
            In::new(&mut input, &mut recover, &mut output),
            type_ml,
            caller_stops,
            outer_closes,
            item_origin,
            line_entry,
            fence,
        )
        .expect("accepted contextual TypeExpression");
    if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
        emit_end(&mut output, end);
    }
    let slots = output.recovery_slot_count();
    let diagnostics = output.diagnostic_position();
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    ContextualTypeRun {
        green,
        exit,
        successor_origin,
        remainder: input,
        records,
        slots,
        diagnostics,
        mark,
        same_operators,
    }
}

fn assert_complete_type_recovery(
    source: &str,
    origin: usize,
    expected: &[CommittedRecoveryRecord],
) -> SyntaxNode {
    let run = |frozen| {
        run_contextual_type_snapshot(
            source,
            super::super::type_expr::TypeMlContext::INACTIVE,
            0,
            0,
            origin,
            LineEntry::InLine,
            None,
            frozen,
        )
    };
    let fresh = run(None);
    assert_eq!(fresh.green.to_string(), format!("sentinel{source}"));
    assert_eq!(fresh.records, expected, "{source:?}, origin={origin}");
    assert_eq!(fresh.successor_origin, origin + source.len(), "{source:?}");
    assert_eq!(fresh.remainder, "", "{source:?}");
    assert_eq!(fresh.slots, expected.len());
    assert_eq!(fresh.diagnostics, (Some(expected.len() as u32), 0));
    assert_eq!(fresh.mark, ());
    assert!(fresh.same_operators);
    let NormalizedExit::Complete(Err(Either::Right(fresh_end)), fresh_line) = &fresh.exit else {
        panic!("complete Type must return EOF: {source:?}")
    };
    assert_eq!(*fresh_line, LineEntry::InLine);

    let frozen = frozen_recovery_ids(expected);
    let replay = run(Some(&frozen));
    assert_eq!(replay.green, fresh.green, "{source:?}");
    assert_eq!(replay.records, frozen, "{source:?}");
    assert_eq!(replay.successor_origin, fresh.successor_origin);
    assert_eq!(replay.remainder, fresh.remainder);
    assert_eq!(replay.slots, frozen.len());
    assert_eq!(
        replay.diagnostics,
        (
            Some(frozen.last().map_or(0, |record| record.id.0 + 1)),
            frozen.len()
        )
    );
    assert_eq!(replay.mark, ());
    assert!(replay.same_operators);
    let NormalizedExit::Complete(Err(Either::Right(replayed_end)), replay_line) = &replay.exit
    else {
        panic!("frozen Type must return EOF: {source:?}")
    };
    assert_eq!(replayed_end, fresh_end);
    assert_eq!(replay_line, fresh_line);
    SyntaxNode::new_root(fresh.green)
}

fn assert_parenthesized_t4p_topology(green: &GreenNode, expected: &[(SyntaxKind, Range<usize>)]) {
    let group = SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedTypeGroup)
        .expect("ParenthesizedTypeGroup");
    assert_direct_children_topology(&group, expected);
    assert!(
        !group
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error),
        "{}",
        group.text(),
    );
}

fn assert_direct_children_topology(node: &SyntaxNode, expected: &[(SyntaxKind, Range<usize>)]) {
    let children = node.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children.len(), expected.len());
    for (child, (kind, range)) in children.iter().zip(expected) {
        assert_eq!(child.kind(), *kind, "{children:#?}");
        assert_eq!(
            usize::from(child.text_range().start())..usize::from(child.text_range().end()),
            *range,
            "{children:#?}",
        );
    }
}

fn t4p_seeded_contexts() -> [(&'static str, super::super::type_expr::TypeMlContext); 4] {
    [
        ("inactive", super::super::type_expr::TypeMlContext::INACTIVE),
        (
            "outer-active",
            super::super::type_expr::TypeMlContext::outer_active_for_test(),
        ),
        (
            "outer-dormant",
            super::super::type_expr::TypeMlContext::outer_dormant_for_test(),
        ),
        (
            "non-TypeApply",
            super::super::type_expr::TypeMlContext::non_type_apply_active_for_test(),
        ),
    ]
}

fn run_required_type_with_outer_boundary_and_recoveries<'source, 'frozen>(
    source: &'source str,
    outer_boundary: super::super::type_expr::TypeOuterBoundary,
    pipe_lexical: bool,
    frozen: Option<&'frozen [CommittedRecoveryRecord]>,
) -> (
    GreenNode,
    NormalizedExit,
    bool,
    usize,
    &'source str,
    Vec<CommittedRecoveryRecord>,
    usize,
    (Option<u32>, usize),
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut output = match frozen {
        Some(frozen) => GreenNodeBuilder::reconcile(frozen),
        None => GreenNodeBuilder::new(),
    };
    output.start_node(SyntaxKind::Root.into());
    let (primary, primary_successor, line_entry) =
        super::super::type_expr::type_nud_item_normalized(
            In::new(&mut input, &mut recover, &mut output),
            0,
            LineEntry::InLine,
            None,
        );
    let continuation_entry =
        super::super::driver::suffix_marker(In::new(&mut input, &mut recover, &mut output));
    let (exit, primary_found) = if pipe_lexical {
        super::super::type_expr::required_variant_payload_type_normalized(
            In::new(&mut input, &mut recover, &mut output),
            primary,
            0,
            super::super::type_expr::TypeMlContext::INACTIVE,
            outer_boundary,
            primary_successor,
            line_entry,
            None,
        )
    } else {
        super::super::type_expr::required_type_expr_with_caller_stops_and_outer_boundary_normalized(
            In::new(&mut input, &mut recover, &mut output),
            primary,
            0,
            0,
            outer_boundary,
            primary_successor,
            line_entry,
            None,
        )
    };
    let successor_origin = super::super::driver::advanced_origin(
        primary_successor,
        continuation_entry,
        In::new(&mut input, &mut recover, &mut output),
    );
    let slots = output.recovery_slot_count();
    let diagnostics = output.diagnostic_position();
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    (
        green,
        exit,
        primary_found,
        successor_origin,
        input,
        records,
        slots,
        diagnostics,
    )
}

fn commit_record_draft(output: &mut GreenNodeBuilder<'_>, record: &CommittedRecoveryRecord) {
    output.commit_recovery(super::super::output::RecoveryDraft::new(
        record.site.clone(),
        record.kind,
        record.unexpected.clone(),
        record.expectations.clone(),
        record.primary_expectation,
    ));
}

fn seed_identifier(output: &mut GreenNodeBuilder<'_>) {
    output.start_node(SyntaxKind::IdentifierExpression.into());
    output.token(SyntaxKind::Identifier.into(), "sentinel");
    output.finish_node();
}

fn scan_type_item_control<'source>(
    source: &'source str,
    item_origin: usize,
    operators: &OperatorTable,
) -> (Item, usize, LineEntry, &'source str, (), bool) {
    scan_type_item_control_with_pipe_lexical(source, item_origin, operators, false)
}

fn scan_type_item_control_with_pipe_lexical<'source>(
    source: &'source str,
    item_origin: usize,
    operators: &OperatorTable,
    pipe_lexical: bool,
) -> (Item, usize, LineEntry, &'source str, (), bool) {
    let mut input = source;
    let mut recover = Recover::new(operators);
    let mark = recover.mark();
    let same_operators = std::ptr::eq(recover.operators(), operators);
    let super::super::current_item::CurrentItem {
        item,
        next_line_entry,
    } = super::super::current_item::current_item(
        In::new(&mut input, &mut recover, ()),
        item_origin,
        LineEntry::InLine,
        None,
        |mut lex, leading, origin, fence, _| {
            if pipe_lexical && let Some(pipe) = lex.token(super::super::lexer::scan_exact_pipe) {
                return Some(super::super::current_item::AcceptedPayload {
                    payload: super::super::current_item::CurrentPayload::Token(pipe),
                    next_line_entry: LineEntry::InLine,
                });
            }
            super::super::lexer::scan_type_nud_payload(lex, leading, origin, fence)
        },
    )
    .expect("control Type Item scan");
    let successor_origin = item_origin
        .checked_add(source.len() - input.len())
        .expect("control Type successor origin");
    (
        item,
        successor_origin,
        next_line_entry,
        input,
        mark,
        same_operators,
    )
}

fn parenthesized_group(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedTypeGroup)
        .expect("parenthesized Type group")
}

fn assert_outer_parenthesized_close(source: &str, item_error: Option<Range<usize>>) {
    let close_at = source.find('}').expect("outer right brace");
    let mut expected = vec![expected_type_error(
        0,
        TypeRole::PolymorphicVariantTagName,
        2..close_at,
    )];
    if let Some(range) = item_error {
        expected.push(pe_recovery::item(1, false, range, true));
    }
    expected.push(expected_parenthesized_close(
        expected.len() as u32,
        close_at,
    ));
    let (green, exit, records) = run_type_with_recoveries(source, None);
    assert_eq!(green.to_string(), source, "{source:?}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
    assert_eq!(records, expected, "{source:?}");
    assert_eq!(
        parenthesized_group(&green)
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1,
        "{source:?}"
    );
}

fn assert_local_parenthesized_close(source: &str, item_error: Option<Range<usize>>) {
    // An unclaimed close belongs to P/E recovery, not to an unknown caller.
    let at = source.find(']').expect("unclaimed mismatched close");
    let mut expected = Vec::new();
    if let Some(range) = item_error {
        expected.push(pe_recovery::item(0, false, range, true));
    }
    expected.push(pe_recovery::close(
        expected.len() as u32,
        false,
        at..at + 1,
        Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
            Delimiter::Bracket,
        ))),
    ));
    expected.push(expected_parenthesized_close(
        expected.len() as u32,
        source.len(),
    ));
    let root = assert_complete_type_recovery(source, 0, &expected);
    let group = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedTypeGroup)
        .unwrap();
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(group.children().any(|node| {
        node.kind() == SyntaxKind::Error
            && node
                .first_token()
                .is_some_and(|token| token.kind() == SyntaxKind::RBracket)
    }));
}

#[test]
fn required_type_primary_publishes_fresh_and_frozen_malformed_records() {
    let malformed = expected_required_type_primary_error(
        0,
        0..1,
        Arc::from([UnexpectedSyntax::Token {
            range: 0..1,
            category: UnexpectedCategory::OtherCharacter,
        }]),
    );
    let (green, exit, primary_found, remainder, records) =
        run_required_type_with_recoveries("@A", 0, LineEntry::InLine, None, None);
    assert_eq!(green.to_string(), "@A");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
    ));
    assert!(primary_found);
    assert_eq!(remainder, "");
    assert_eq!(records, [malformed.clone()]);
    let root = SyntaxNode::new_root(green.clone());
    let error = root
        .children()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("required Type-primary Error");
    assert_eq!(error.text(), "@");
    assert_eq!(
        error
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [(SyntaxKind::Unknown, "@".to_owned())]
    );
    let (frozen_green, frozen_exit, frozen_found, frozen_remainder, frozen_records) =
        run_required_type_with_recoveries(
            "@A",
            0,
            LineEntry::InLine,
            None,
            Some(std::slice::from_ref(&malformed)),
        );
    assert_eq!(frozen_green, green);
    assert!(matches!(
        frozen_exit,
        NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
    ));
    assert!(frozen_found);
    assert_eq!(frozen_remainder, "");
    assert_eq!(frozen_records, [malformed]);
}

#[test]
fn required_type_primary_error_run_keeps_item_evidence_and_cst_order() {
    let expected = expected_required_type_primary_error(
        0,
        0..3,
        Arc::from([
            UnexpectedSyntax::Token {
                range: 0..1,
                category: UnexpectedCategory::OtherCharacter,
            },
            UnexpectedSyntax::Token {
                range: 1..3,
                category: UnexpectedCategory::Punctuation(PunctuationEvidence::Dot),
            },
        ]),
    );
    let (green, exit, primary_found, remainder, records) =
        run_required_type_with_recoveries("@ .A", 0, LineEntry::InLine, None, None);
    assert_eq!(green.to_string(), "@ .A");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
    ));
    assert!(primary_found);
    assert_eq!(remainder, "");
    assert_eq!(records, [expected.clone()]);
    let error = SyntaxNode::new_root(green.clone())
        .children()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("one contiguous required Type Error");
    assert_eq!(error.text(), "@ .");
    assert_eq!(
        error
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Unknown, "@".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Dot, ".".to_owned()),
        ]
    );
    let (frozen_green, _, frozen_found, frozen_remainder, frozen_records) =
        run_required_type_with_recoveries(
            "@ .A",
            0,
            LineEntry::InLine,
            None,
            Some(std::slice::from_ref(&expected)),
        );
    assert_eq!(frozen_green, green);
    assert!(frozen_found);
    assert_eq!(frozen_remainder, "");
    assert_eq!(frozen_records, [expected]);
}

#[test]
fn required_type_primary_error_stops_before_a_pending_lexical_boundary() {
    let expected = expected_required_type_primary_error(
        0,
        0..1,
        Arc::from([UnexpectedSyntax::Token {
            range: 0..1,
            category: UnexpectedCategory::OtherCharacter,
        }]),
    );
    let (green, exit, primary_found, remainder, records) =
        run_required_type_with_recoveries("@ ,A", 0, LineEntry::InLine, None, None);
    assert_eq!(green.to_string(), "@");
    let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit else {
        panic!("required Type Error must preserve its pending comma")
    };
    assert!(!primary_found);
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Comma));
    assert_eq!(item.payload_view().spelling(), Some(","));
    assert_eq!(emit_pending_leading_text(&mut item), " ");
    assert_eq!(remainder, "A");
    assert_eq!(records, [expected.clone()]);
    let error = SyntaxNode::new_root(green.clone())
        .children()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("required Type-primary Error");
    assert_eq!(error.text(), "@");
    assert_eq!(
        error
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [(SyntaxKind::Unknown, "@".to_owned())]
    );

    let (frozen_green, frozen_exit, frozen_found, frozen_remainder, frozen_records) =
        run_required_type_with_recoveries(
            "@ ,A",
            0,
            LineEntry::InLine,
            None,
            Some(std::slice::from_ref(&expected)),
        );
    assert_eq!(frozen_green, green);
    let NormalizedExit::Complete(Err(Either::Left(mut frozen_item)), LineEntry::InLine) =
        frozen_exit
    else {
        panic!("frozen required Type Error must preserve its pending comma")
    };
    assert!(!frozen_found);
    assert_eq!(
        frozen_item.payload_view().token_kind(),
        Some(TokenKind::Comma)
    );
    assert_eq!(emit_pending_leading_text(&mut frozen_item), " ");
    assert_eq!(frozen_remainder, "A");
    assert_eq!(frozen_records, [expected]);
}

#[test]
fn required_type_primary_preserves_boundaries_and_accepts_an_ordinary_primary() {
    for (source, kind) in [
        (",A", TokenKind::Comma),
        (";A", TokenKind::Semicolon),
        (")A", TokenKind::RParen),
        ("]A", TokenKind::RBracket),
        ("}A", TokenKind::RBrace),
        ("=A", TokenKind::Equals),
    ] {
        let (green, exit, primary_found, remainder, records) =
            run_required_type_with_recoveries(source, 0, LineEntry::InLine, None, None);
        assert_eq!(green.to_string(), "", "{source:?}");
        let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
            panic!("required Type boundary must remain pending: {source:?}")
        };
        assert_eq!(item.payload_view().token_kind(), Some(kind), "{source:?}");
        assert_eq!(remainder, "A", "{source:?}");
        assert!(!primary_found, "{source:?}");
        assert!(records.is_empty(), "{source:?}");
        let type_expr = SyntaxNode::new_root(green)
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeExpression)
            .expect("raw missing required TypeExpression");
        assert_eq!(
            type_expr
                .children()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [SyntaxKind::Missing],
            "{source:?}"
        );
    }

    let (green, exit, primary_found, remainder, records) =
        run_required_type_with_recoveries("A", 0, LineEntry::InLine, None, None);
    assert_eq!(green.to_string(), "A");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
    ));
    assert!(primary_found);
    assert_eq!(remainder, "");
    assert!(records.is_empty());

    let (green, exit, primary_found, remainder, records) =
        run_required_type_with_recoveries("", 0, LineEntry::InLine, None, None);
    assert_eq!(green.to_string(), "");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
    ));
    assert!(!primary_found);
    assert_eq!(remainder, "");
    assert!(records.is_empty());
    assert_eq!(
        SyntaxNode::new_root(green)
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeExpression)
            .expect("raw EOF missing TypeExpression")
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Missing]
    );
}

#[test]
fn required_type_primary_abstract_boundary_is_missing_and_unconsumed() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let source = "> > \n> > ```\nouter";
    let (green, exit, primary_found, remainder, records) =
        run_required_type_with_recoveries(source, 0, LineEntry::PhysicalStart, Some(&fence), None);
    assert_eq!(green.to_string(), "");
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart) = exit else {
        panic!("required Type must preserve the fence boundary")
    };
    assert!(item.payload_view().is_boundary());
    assert!(item.leading_view().has_ordinary_newline());
    assert!(!primary_found);
    assert_eq!(remainder, "> > ```\nouter");
    assert!(records.is_empty());
    assert_eq!(
        SyntaxNode::new_root(green)
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeExpression)
            .expect("raw fence missing TypeExpression")
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Missing]
    );
}

#[test]
fn pattern_annotation_keeps_caller_missing_raw_and_t1_error_typed() {
    let (missing_green, missing_exit, missing_records) = run_pattern_with_recoveries("x:", None);
    assert_eq!(missing_green.to_string(), "x:");
    assert!(matches!(missing_exit, Err(Either::Right(_))));
    assert!(missing_records.is_empty());
    let missing_annotation = SyntaxNode::new_root(missing_green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
        .expect("pattern Type annotation");
    assert_eq!(
        missing_annotation
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        !missing_annotation
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );

    let expected = expected_required_type_primary_error(
        0,
        3..4,
        Arc::from([UnexpectedSyntax::Token {
            range: 3..4,
            category: UnexpectedCategory::OtherCharacter,
        }]),
    );
    let (error_green, error_exit, error_records) = run_pattern_with_recoveries("x: @A", None);
    assert_eq!(error_green.to_string(), "x: @A");
    assert!(matches!(error_exit, Err(Either::Right(_))));
    assert_eq!(error_records, [expected.clone()]);
    let annotation = SyntaxNode::new_root(error_green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
        .expect("pattern Type annotation");
    let errors = annotation
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Error)
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text(), "@");
    assert!(
        !annotation
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    let (frozen_green, frozen_exit, frozen_records) =
        run_pattern_with_recoveries("x: @A", Some(std::slice::from_ref(&expected)));
    assert_eq!(frozen_green, error_green);
    assert!(matches!(frozen_exit, Err(Either::Right(_))));
    assert_eq!(frozen_records, [expected]);
}

#[test]
fn rb_t_required_type_probe_rejection_preserves_output_and_input() {
    let operators = OperatorTable::empty();
    let frozen = [expected_parenthesized_close(7, 0)];

    let mut candidate_input = "@A";
    let mut candidate_recover = Recover::new(&operators);
    let candidate_mark = candidate_recover.mark();
    let candidate_operators = std::ptr::eq(candidate_recover.operators(), &operators);
    let mut candidate_output = GreenNodeBuilder::reconcile(&frozen);
    candidate_output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut candidate_output);
    candidate_output.start_node(SyntaxKind::Missing.into());
    candidate_output.finish_node();
    commit_record_draft(&mut candidate_output, &frozen[0]);
    let before_slots = candidate_output.recovery_slot_count();
    let before_diagnostics = candidate_output.diagnostic_position();
    let exit = super::super::type_expr::type_expr(In::new(
        &mut candidate_input,
        &mut candidate_recover,
        &mut candidate_output,
    ));
    assert!(exit.is_none());
    let candidate_slots = candidate_output.recovery_slot_count();
    let candidate_diagnostics = candidate_output.diagnostic_position();
    candidate_output.finish_node();
    let (candidate_green, candidate_records) = candidate_output.finish_with_recoveries();

    let control_input = "@A";
    let control_recover = Recover::new(&operators);
    let control_mark = control_recover.mark();
    let control_operators = std::ptr::eq(control_recover.operators(), &operators);
    let mut control_output = GreenNodeBuilder::reconcile(&frozen);
    control_output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut control_output);
    control_output.start_node(SyntaxKind::Missing.into());
    control_output.finish_node();
    commit_record_draft(&mut control_output, &frozen[0]);
    let control_slots = control_output.recovery_slot_count();
    let control_diagnostics = control_output.diagnostic_position();
    control_output.finish_node();
    let (control_green, control_records) = control_output.finish_with_recoveries();

    assert_eq!(candidate_green, control_green);
    assert_eq!(candidate_records, control_records);
    assert_eq!(candidate_slots, control_slots);
    assert_eq!(candidate_diagnostics, control_diagnostics);
    assert_eq!(candidate_input, control_input);
    assert_eq!(candidate_mark, control_mark);
    assert_eq!(candidate_mark, ());
    assert!(candidate_operators && control_operators);
    assert_eq!(candidate_slots, before_slots);
    assert_eq!(candidate_diagnostics, before_diagnostics);
    assert_eq!(candidate_diagnostics, (Some(8), 1));
    assert_eq!(candidate_records, frozen);
}

#[test]
fn rb_t_arrow_rhs_rejected_retry_seal_preserves_successor_vector() {
    let operators = OperatorTable::empty();
    let frozen = [expected_type_expression_error(
        7,
        TypeRole::ArrowRhs,
        4..5,
        Arc::from([UnexpectedSyntax::Token {
            range: 4..5,
            category: UnexpectedCategory::OtherCharacter,
        }]),
    )];

    let mut candidate_input = "A ->@ with";
    let mut candidate_recover = Recover::new(&operators);
    let candidate_mark = candidate_recover.mark();
    let candidate_operators = std::ptr::eq(candidate_recover.operators(), &operators);
    let mut candidate_output = GreenNodeBuilder::reconcile(&frozen);
    candidate_output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut candidate_output);
    let (primary, primary_origin, primary_line) = super::super::type_expr::type_nud_item_normalized(
        In::new(
            &mut candidate_input,
            &mut candidate_recover,
            &mut candidate_output,
        ),
        0,
        LineEntry::InLine,
        None,
    );
    let continuation_entry = super::super::driver::suffix_marker(In::new(
        &mut candidate_input,
        &mut candidate_recover,
        &mut candidate_output,
    ));
    let (candidate_exit, primary_found) =
        super::super::type_expr::required_type_expr_with_caller_stops_and_outer_boundary_normalized(
            In::new(
                &mut candidate_input,
                &mut candidate_recover,
                &mut candidate_output,
            ),
            primary,
            0,
            0,
            super::super::type_expr::TypeOuterBoundary::WITH,
            primary_origin,
            primary_line,
            None,
        );
    let candidate_origin = super::super::driver::advanced_origin(
        primary_origin,
        continuation_entry,
        In::new(
            &mut candidate_input,
            &mut candidate_recover,
            &mut candidate_output,
        ),
    );
    let NormalizedExit::Complete(Err(Either::Left(candidate_item)), candidate_line) =
        candidate_exit
    else {
        panic!("outer-owned Arrow retry must remain pending")
    };
    assert!(primary_found);
    let candidate_slots = candidate_output.recovery_slot_count();
    let candidate_diagnostics = candidate_output.diagnostic_position();
    candidate_output.finish_node();
    let (candidate_green, candidate_records) = candidate_output.finish_with_recoveries();

    let (
        control_item,
        control_origin,
        control_line,
        control_input,
        control_mark,
        control_operators,
    ) = scan_type_item_control(" with", 5, &operators);
    let mut control_output = GreenNodeBuilder::reconcile(&frozen);
    control_output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut control_output);
    control_output.start_node(SyntaxKind::TypeExpression.into());
    control_output.token(SyntaxKind::Identifier.into(), "A");
    control_output.start_node(SyntaxKind::TypeArrowTail.into());
    control_output.token(SyntaxKind::Whitespace.into(), " ");
    control_output.token(SyntaxKind::Arrow.into(), "->");
    control_output.start_node(SyntaxKind::Error.into());
    control_output.token(SyntaxKind::Unknown.into(), "@");
    control_output.finish_node();
    commit_record_draft(&mut control_output, &frozen[0]);
    control_output.finish_node();
    control_output.finish_node();
    let control_slots = control_output.recovery_slot_count();
    let control_diagnostics = control_output.diagnostic_position();
    control_output.finish_node();
    let (control_green, control_records) = control_output.finish_with_recoveries();

    assert_eq!(candidate_green, control_green);
    assert_eq!(candidate_records, control_records);
    assert_eq!(candidate_records, frozen);
    assert_eq!(candidate_slots, control_slots);
    assert_eq!(candidate_slots, 1);
    assert_eq!(candidate_diagnostics, control_diagnostics);
    assert_eq!(candidate_diagnostics, (Some(8), 1));
    assert_eq!(candidate_input, control_input);
    assert_eq!(candidate_input, "");
    assert_eq!(candidate_item, control_item);
    assert_eq!(candidate_item.payload_view().spelling(), Some("with"));
    assert_eq!(candidate_item.leading_view().remaining_physical_parts(), 1);
    assert!(candidate_item.leading_view().has_ordinary_trivia());
    assert!(!candidate_item.leading_view().has_ordinary_newline());
    assert_eq!(candidate_origin, control_origin);
    assert_eq!(candidate_origin, 10);
    assert_eq!(candidate_line, control_line);
    assert_eq!(candidate_line, LineEntry::InLine);
    assert_eq!(candidate_mark, control_mark);
    assert_eq!(candidate_mark, ());
    assert!(candidate_operators && control_operators);
}

#[test]
fn ordinary_type_payload_does_not_classify_pipe_as_a_contextual_separator() {
    let (green, exit) = run_type("T | U");
    assert_eq!(green.to_string(), "T");
    let Some(Err(Either::Left(item))) = exit else {
        panic!("ordinary Type must hand its unowned raw pipe to the caller")
    };
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Unknown));
    assert_eq!(item.payload_view().spelling(), Some("|"));
}

#[test]
fn type_expression_keeps_fixed_tails_in_source_order() {
    let source = "List(Int)::Result Arg -> Out -> Final";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let top = top_type_expression(&green);
    assert_eq!(
        top.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::TypeCallTail,
            SyntaxKind::TypePathTail,
            SyntaxKind::TypeApplyArgument,
            SyntaxKind::TypeArrowTail,
        ]
    );
    let arrows = top
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::TypeArrowTail)
        .count();
    assert_eq!(arrows, 2);
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Identifier, "List".to_owned()),
            (SyntaxKind::LParen, "(".to_owned()),
            (SyntaxKind::Identifier, "Int".to_owned()),
            (SyntaxKind::RParen, ")".to_owned()),
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Identifier, "Result".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "Arg".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Arrow, "->".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "Out".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Arrow, "->".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "Final".to_owned()),
        ]
    );
}

#[test]
fn type_expression_accepts_sigil_and_numeric_atoms_but_not_numeric_path_segments() {
    let source = "$value::'result _hidden 42";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::SigilIdentifier, "$value".to_owned()),
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::SigilIdentifier, "'result".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::SigilIdentifier, "_hidden".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Integer, "42".to_owned()),
        ]
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeApplyArgument)
            .count(),
        2
    );
}

#[test]
fn type_apply_scope_keeps_adjacent_and_spaced_paths_distinct() {
    let adjacent = run_type("F A::B").0;
    let spaced = run_type("F A ::B").0;
    assert_eq!(adjacent.to_string(), "F A::B");
    assert_eq!(spaced.to_string(), "F A ::B");

    let adjacent_top = top_type_expression(&adjacent);
    let adjacent_apply = adjacent_top
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeApplyArgument)
        .expect("adjacent apply");
    assert!(
        adjacent_apply
            .descendants()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );
    assert!(
        !adjacent_top
            .children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );

    let spaced_top = top_type_expression(&spaced);
    assert!(
        spaced_top
            .children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );
}

#[test]
fn type_call_and_group_keep_explicit_and_implicit_boundaries() {
    let source = "T(A, B; C) (D\nE)";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let top = top_type_expression(&green);
    let call = top
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("type call");
    assert_eq!(
        call.children()
            .filter(|node| node.kind() == SyntaxKind::TypeExpression)
            .count(),
        3
    );
    assert_eq!(
        call.children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::LParen, "(".to_owned()),
            (SyntaxKind::Comma, ",".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Semicolon, ";".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::RParen, ")".to_owned()),
        ]
    );
    let apply = top
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeApplyArgument)
        .expect("group apply");
    let group = apply
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedTypeGroup)
        .expect("parenthesized type group");
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeExpression)
            .count(),
        2
    );
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn type_path_tail_recovers_its_mandatory_segment() {
    for (source, recovery) in [
        ("A::", SyntaxKind::Missing),
        ("A::123", SyntaxKind::Error),
        ("A::@Name", SyntaxKind::Error),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let path = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypePathTail)
            .expect("type path tail");
        assert_eq!(
            path.children()
                .filter(|node| node.kind() == recovery)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("A::::Name");
    assert_eq!(green.to_string(), "A::::Name");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypePathTail)
            .count(),
        2
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run_type("A:: ");
    assert_eq!(green.to_string(), "A:: ");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let path = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypePathTail)
        .expect("type path tail");
    assert_eq!(
        path.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
        ]
    );
}

#[test]
fn type_path_segment_missing_records_use_exact_owner_anchors_fresh_and_frozen() {
    for (source, emitted, at) in [("A::", "A::", 3), ("A:: ", "A:: ", 4), ("A:: )", "A:: ", 4)] {
        let expected = expected_type_path_segment_recovery(0, RecoveryKind::Missing, at..at);
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), emitted, "{source:?}");
        assert!(matches!(exit, Some(Err(_))), "{source:?}");
        assert_eq!(records, [expected.clone()], "{source:?}");
        let path = SyntaxNode::new_root(green.clone())
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypePathTail)
            .expect("TypePathTail");
        let missing = path
            .children()
            .find(|node| node.kind() == SyntaxKind::Missing)
            .expect("PathSegment Missing");
        assert_eq!(
            usize::from(missing.text_range().start())..usize::from(missing.text_range().end()),
            at..at,
            "{source:?}",
        );
        let frozen_expected = expected_type_path_segment_recovery(7, RecoveryKind::Missing, at..at);
        let (frozen_green, _, frozen_records) =
            run_type_with_recoveries(source, Some(std::slice::from_ref(&frozen_expected)));
        assert_eq!(frozen_green, green, "{source:?}");
        assert_eq!(frozen_records, [frozen_expected], "{source:?}");
    }

    let (green, exit, primary_found, _, _, records, _, _) =
        run_required_type_with_outer_boundary_and_recoveries(
            "A:: =",
            super::super::type_expr::TypeOuterBoundary::EQUALS,
            false,
            None,
        );
    assert!(primary_found);
    let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) = exit else {
        panic!("outer Equals remains pending")
    };
    assert_eq!(green.to_string(), "A::");
    assert_eq!(
        records,
        [expected_type_path_segment_recovery(
            0,
            RecoveryKind::Missing,
            3..3
        )]
    );
    assert_eq!(pending.payload_view().spelling(), Some("="));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");

    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let source = "> > A::";
    let expected = expected_type_path_segment_recovery(0, RecoveryKind::Missing, 7..7);
    let (green, exit, remainder, records) = run_type_normalized_with_recoveries(
        source,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
        None,
    );
    assert_eq!(green.to_string(), "> > A::");
    assert!(exit.is_some());
    assert_eq!(remainder, "");
    assert_eq!(records, [expected.clone()]);
    let (frozen_green, _, frozen_remainder, frozen_records) = run_type_normalized_with_recoveries(
        source,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
        Some(std::slice::from_ref(&expected)),
    );
    assert_eq!(frozen_green, green);
    assert_eq!(frozen_remainder, remainder);
    assert_eq!(frozen_records, [expected]);

    let boundary_source = "> > A::\n> > ```\nouter\n";
    let boundary_expected = expected_type_path_segment_recovery(0, RecoveryKind::Missing, 8..8);
    let (boundary_green, boundary_exit, boundary_remainder, boundary_records) =
        run_type_normalized_with_recoveries(
            boundary_source,
            0,
            LineEntry::PhysicalStart,
            Some(&fence),
            None,
        );
    assert_eq!(boundary_green.to_string(), "> > A::");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        boundary_exit
    else {
        panic!("PathSegment preserves the abstract fence boundary")
    };
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(boundary_remainder, "> > ```\nouter\n");
    assert_eq!(boundary_records, [boundary_expected.clone()]);
    let (frozen_green, _, frozen_remainder, frozen_records) = run_type_normalized_with_recoveries(
        boundary_source,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
        Some(std::slice::from_ref(&boundary_expected)),
    );
    assert_eq!(frozen_green, boundary_green);
    assert_eq!(frozen_remainder, boundary_remainder);
    assert_eq!(frozen_records, [boundary_expected]);
}

#[test]
fn type_contextual_names_belong_to_paths_and_nested_calls() {
    use super::super::type_expr::TypeOuterBoundary;

    for (word, boundary) in [
        ("with", TypeOuterBoundary::WITH),
        ("derives", TypeOuterBoundary::DERIVES),
        ("via", TypeOuterBoundary::VIA),
        ("impl", TypeOuterBoundary::IMPL),
    ] {
        let bodies = [
            format!("A::{word}"),
            format!("A:: {word}"),
            format!("A::/*c*/{word}"),
            format!("T({word})"),
            format!("T(A {word})"),
            format!("T(A, {word})"),
        ];
        for body in bodies {
            for suffix in ["".to_owned(), format!(" {word}")] {
                let source = format!("{body}{suffix}");
                let mut fresh_green = None;
                for frozen in [None, Some([].as_slice())] {
                    let (green, exit, accepted, origin, remainder, records, slots, diagnostics) =
                        run_required_type_with_outer_boundary_and_recoveries(
                            &source, boundary, false, frozen,
                        );
                    assert!(accepted, "{source:?}");
                    assert_eq!(green.to_string(), body, "{source:?}");
                    assert_eq!(origin, source.len(), "{source:?}");
                    assert_eq!(remainder, "", "{source:?}");
                    assert!(records.is_empty(), "{source:?}: {records:?}");
                    assert_eq!(slots, 0);
                    assert_eq!(diagnostics, (Some(0), 0));
                    if suffix.is_empty() {
                        assert!(
                            matches!(
                                exit,
                                NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
                            ),
                            "{source:?}"
                        );
                    } else {
                        let NormalizedExit::Complete(
                            Err(Either::Left(mut pending)),
                            LineEntry::InLine,
                        ) = exit
                        else {
                            panic!(
                                "outer contextual word must resume after its nested owner: {source:?}"
                            )
                        };
                        assert_eq!(pending.payload_view().spelling(), Some(word));
                        assert_eq!(emit_pending_leading_text(&mut pending), " ");
                    }
                    let root = SyntaxNode::new_root(green.clone());
                    assert!(
                        !root.descendants().any(|node| {
                            matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error)
                        }),
                        "{source:?}"
                    );
                    let owner = if body.starts_with("A::") {
                        SyntaxKind::TypePathTail
                    } else {
                        SyntaxKind::TypeCallTail
                    };
                    let node = root
                        .descendants()
                        .find(|node| node.kind() == owner)
                        .expect("path or Call owner");
                    assert!(node.descendants_with_tokens().any(|child| {
                        child.kind() == SyntaxKind::Identifier && child.to_string() == word
                    }));
                    if let Some(fresh) = &fresh_green {
                        assert_eq!(&green, fresh);
                    } else {
                        fresh_green = Some(green);
                    }
                }
            }
        }
    }
}

#[test]
fn type_contextual_path_newlines_remain_outer_owned() {
    use super::super::type_expr::TypeOuterBoundary;

    for (word, boundary) in [
        ("with", TypeOuterBoundary::WITH),
        ("derives", TypeOuterBoundary::DERIVES),
        ("via", TypeOuterBoundary::VIA),
        ("impl", TypeOuterBoundary::IMPL),
    ] {
        for gap in ["\n", "\n  ", "\r\n  ", "/*\n*/"] {
            let source = format!("A::{gap}{word}");
            let expected = [expected_type_path_segment_recovery(
                0,
                RecoveryKind::Missing,
                3..3,
            )];
            let frozen = frozen_recovery_ids(&expected);
            for (input_records, expected_records) in [
                (None, expected.as_slice()),
                (Some(frozen.as_slice()), frozen.as_slice()),
            ] {
                let (green, exit, accepted, origin, remainder, records, slots, _) =
                    run_required_type_with_outer_boundary_and_recoveries(
                        &source,
                        boundary,
                        false,
                        input_records,
                    );
                assert!(accepted);
                assert_eq!(green.to_string(), "A::", "{source:?}");
                assert_eq!(origin, source.len());
                assert_eq!(remainder, "");
                assert_eq!(records, expected_records);
                assert_eq!(slots, 1);
                let NormalizedExit::Complete(Err(Either::Left(mut pending)), _) = exit else {
                    panic!("newline contextual boundary remains pending: {source:?}")
                };
                assert_eq!(pending.payload_view().spelling(), Some(word));
                assert_eq!(emit_pending_leading_text(&mut pending), gap);
            }
        }
    }
}

#[test]
fn type_path_segment_error_records_preserve_legacy_continuation_and_native_children() {
    for (source, range, error_children, retry_in_path, retry_in_apply) in [
        ("A::@", 3..4, vec![(SyntaxKind::Unknown, "@")], false, false),
        (
            "A::123",
            3..6,
            vec![(SyntaxKind::Integer, "123")],
            false,
            false,
        ),
        ("A::@B", 3..4, vec![(SyntaxKind::Unknown, "@")], true, false),
        (
            "A::@ B",
            3..4,
            vec![(SyntaxKind::Unknown, "@")],
            false,
            true,
        ),
        (
            "A::@\n  B",
            3..4,
            vec![(SyntaxKind::Unknown, "@")],
            true,
            false,
        ),
        (
            "A::@\r\n  B",
            3..4,
            vec![(SyntaxKind::Unknown, "@")],
            true,
            false,
        ),
        (
            "A::@@B",
            3..5,
            vec![(SyntaxKind::Unknown, "@"), (SyntaxKind::Unknown, "@")],
            true,
            false,
        ),
        (
            "A::@/*x*/B",
            3..9,
            vec![
                (SyntaxKind::Unknown, "@"),
                (SyntaxKind::BlockComment, "/*x*/"),
            ],
            true,
            false,
        ),
        (
            "A::@/*x*/ B",
            3..9,
            vec![
                (SyntaxKind::Unknown, "@"),
                (SyntaxKind::BlockComment, "/*x*/"),
            ],
            false,
            true,
        ),
        (
            "A::@/*x*/@B",
            3..10,
            vec![
                (SyntaxKind::Unknown, "@"),
                (SyntaxKind::BlockComment, "/*x*/"),
                (SyntaxKind::Unknown, "@"),
            ],
            true,
            false,
        ),
        (
            "A::@/*a*//*b*/ B",
            3..14,
            vec![
                (SyntaxKind::Unknown, "@"),
                (SyntaxKind::BlockComment, "/*a*/"),
                (SyntaxKind::BlockComment, "/*b*/"),
            ],
            false,
            true,
        ),
        (
            "A::@/*x*/ //note\n  B",
            3..4,
            vec![(SyntaxKind::Unknown, "@")],
            true,
            false,
        ),
    ] {
        let expected = expected_type_path_segment_recovery(0, RecoveryKind::Error, range.clone());
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(records, [expected], "{source:?}");
        let root = SyntaxNode::new_root(green.clone());
        let path = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypePathTail)
            .expect("TypePathTail");
        let error = path
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("PathSegment Error");
        assert_eq!(
            usize::from(error.text_range().start())..usize::from(error.text_range().end()),
            range,
            "{source:?}",
        );
        assert_eq!(
            error
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .map(|token| (token.kind(), token.text().to_owned()))
                .collect::<Vec<_>>(),
            error_children
                .into_iter()
                .map(|(kind, text)| (kind, text.to_owned()))
                .collect::<Vec<_>>(),
            "{source:?}",
        );
        let b = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == SyntaxKind::Identifier && token.text() == "B");
        assert_eq!(b.is_some(), retry_in_path || retry_in_apply, "{source:?}");
        if let Some(b) = b {
            let in_path = b.parent_ancestors().any(|ancestor| ancestor == path);
            let in_apply = b
                .parent_ancestors()
                .any(|ancestor| ancestor.kind() == SyntaxKind::TypeApplyArgument);
            assert_eq!(in_path, retry_in_path, "{source:?}");
            assert_eq!(in_apply, retry_in_apply, "{source:?}");
            if retry_in_apply {
                let space = root
                    .descendants_with_tokens()
                    .filter_map(|element| element.into_token())
                    .find(|token| {
                        token.kind() == SyntaxKind::Whitespace
                            && usize::from(token.text_range().start()) == range.end
                    })
                    .expect("outer TypeApply space");
                assert!(!space.parent_ancestors().any(|ancestor| ancestor == error));
                assert!(
                    space
                        .parent_ancestors()
                        .any(|ancestor| { ancestor.kind() == SyntaxKind::TypeApplyArgument })
                );
            }
        }

        let frozen_expected = expected_type_path_segment_recovery(
            7,
            RecoveryKind::Error,
            records[0].site.range.clone(),
        );
        let (frozen_green, _, frozen_records) =
            run_type_with_recoveries(source, Some(std::slice::from_ref(&frozen_expected)));
        assert_eq!(frozen_green, green, "{source:?}");
        assert_eq!(frozen_records, [frozen_expected], "{source:?}");
    }
}

#[test]
fn type_path_segment_malformed_trivia_ownership_is_phase_aware() {
    let source = "A:: @";
    let expected = expected_type_path_segment_recovery(0, RecoveryKind::Error, 4..5);
    let (green, exit, records) = run_type_with_recoveries(source, None);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(records, [expected]);
    let root = SyntaxNode::new_root(green.clone());
    let path = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypePathTail)
        .expect("TypePathTail");
    let error = path
        .children()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("PathSegment Error");
    assert_eq!(error.text(), "@");
    assert_eq!(
        usize::from(error.text_range().start())..usize::from(error.text_range().end()),
        4..5,
    );
    let initial_space = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::Whitespace)
        .expect("initial PathSegment whitespace");
    assert_eq!(
        usize::from(initial_space.text_range().start())
            ..usize::from(initial_space.text_range().end()),
        3..4,
    );
    assert!(
        initial_space
            .parent_ancestors()
            .any(|ancestor| ancestor == path)
    );
    assert!(
        !initial_space
            .parent_ancestors()
            .any(|ancestor| ancestor == error)
    );
    let frozen = expected_type_path_segment_recovery(7, RecoveryKind::Error, 4..5);
    let (frozen_green, _, frozen_records) =
        run_type_with_recoveries(source, Some(std::slice::from_ref(&frozen)));
    assert_eq!(frozen_green, green);
    assert_eq!(frozen_records, [frozen]);

    for (source, range, error_children) in [
        ("A::@ 123", 3..4, vec![(SyntaxKind::Unknown, "@")]),
        (
            "A::@/*x*/ 123",
            3..9,
            vec![
                (SyntaxKind::Unknown, "@"),
                (SyntaxKind::BlockComment, "/*x*/"),
            ],
        ),
    ] {
        let expected = expected_type_path_segment_recovery(0, RecoveryKind::Error, range.clone());
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(records, [expected], "{source:?}");
        let root = SyntaxNode::new_root(green.clone());
        let path = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypePathTail)
            .expect("TypePathTail");
        let error = path
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("PathSegment Error");
        assert_eq!(
            error
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .map(|token| (token.kind(), token.text().to_owned()))
                .collect::<Vec<_>>(),
            error_children
                .into_iter()
                .map(|(kind, text)| (kind, text.to_owned()))
                .collect::<Vec<_>>(),
            "{source:?}",
        );
        let integer = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == SyntaxKind::Integer && token.text() == "123")
            .expect("outer numeric TypeApply argument");
        assert!(
            integer
                .parent_ancestors()
                .any(|ancestor| ancestor.kind() == SyntaxKind::TypeApplyArgument)
        );
        assert!(!integer.parent_ancestors().any(|ancestor| ancestor == path));
        let gap = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| {
                token.kind() == SyntaxKind::Whitespace
                    && usize::from(token.text_range().start()) == range.end
            })
            .expect("post-error outer TypeApply gap");
        assert!(
            gap.parent_ancestors()
                .any(|ancestor| ancestor.kind() == SyntaxKind::TypeApplyArgument)
        );
        assert!(!gap.parent_ancestors().any(|ancestor| ancestor == error));

        let frozen = expected_type_path_segment_recovery(7, RecoveryKind::Error, range);
        let (frozen_green, _, frozen_records) =
            run_type_with_recoveries(source, Some(std::slice::from_ref(&frozen)));
        assert_eq!(frozen_green, green, "{source:?}");
        assert_eq!(frozen_records, [frozen], "{source:?}");
    }
}

#[test]
fn type_path_segment_valid_controls_publish_no_recovery() {
    for source in ["A::B", "A:: B", "A::'b"] {
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(records.is_empty(), "{source:?}");
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
        );
    }
}

#[test]
fn type_path_segment_shifted_origin_maps_local_cst_to_global_records() {
    for (source, local, global) in [
        ("A::@", 3..4, 18..19),
        ("A::@@B", 3..5, 18..20),
        ("A::@/*x*/ B", 3..9, 18..24),
    ] {
        let (green, exit, primary_found, remainder, records) =
            run_required_type_with_recoveries(source, 15, LineEntry::InLine, None, None);
        assert!(primary_found, "{source:?}");
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
        assert_eq!(remainder, "", "{source:?}");
        assert_eq!(
            records,
            [expected_type_path_segment_recovery(
                0,
                RecoveryKind::Error,
                global.clone()
            )]
        );
        let error = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("shifted PathSegment Error");
        assert_eq!(
            usize::from(error.text_range().start())..usize::from(error.text_range().end()),
            local.clone(),
            "{source:?}",
        );
        assert_eq!(15 + local.start..15 + local.end, global, "{source:?}");
    }
}

#[test]
fn type_path_segment_boundaries_outrank_retry_leading_and_remain_pending() {
    for (source, outer_boundary, pipe_lexical, pending_kind, leading_text) in [
        (
            "A::@ with",
            super::super::type_expr::TypeOuterBoundary::WITH,
            false,
            TokenKind::Identifier,
            " ",
        ),
        (
            "A::@/*x*/ with",
            super::super::type_expr::TypeOuterBoundary::WITH,
            false,
            TokenKind::Identifier,
            "/*x*/ ",
        ),
        (
            "A::@ = Body",
            super::super::type_expr::TypeOuterBoundary::EQUALS,
            false,
            TokenKind::Equals,
            " ",
        ),
        (
            "A::@ | Body",
            super::super::type_expr::TypeOuterBoundary::PIPE,
            true,
            TokenKind::Pipe,
            " ",
        ),
        (
            "A::@ : Body",
            super::super::type_expr::TypeOuterBoundary::STRUCT_BODY,
            false,
            TokenKind::Colon,
            " ",
        ),
        (
            "A::@ ; Body",
            super::super::type_expr::TypeOuterBoundary::VARIANT_BODY,
            false,
            TokenKind::Semicolon,
            " ",
        ),
    ] {
        let (green, exit, primary_found, _, _, records, slots, diagnostics) =
            run_required_type_with_outer_boundary_and_recoveries(
                source,
                outer_boundary,
                pipe_lexical,
                None,
            );
        let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) = exit
        else {
            panic!("outer boundary remains pending: {source:?}")
        };
        assert!(primary_found, "{source:?}");
        assert_eq!(green.to_string(), "A::@", "{source:?}");
        assert_eq!(
            records,
            [expected_type_path_segment_recovery(
                0,
                RecoveryKind::Error,
                3..4,
            )],
            "{source:?}",
        );
        assert_eq!(
            pending.payload_view().token_kind(),
            Some(pending_kind),
            "{source:?}"
        );
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            leading_text,
            "{source:?}"
        );
        assert_eq!(slots, 1, "{source:?}");
        assert_eq!(diagnostics, (Some(1), 0), "{source:?}");
    }

    let operators = OperatorTable::empty();
    for (source, leading_text) in [("A::@ )", " "), ("A::@/*x*/ )", "/*x*/ ")] {
        let mut input = source;
        let mut recover = Recover::new(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (exit, _) = super::super::type_expr::type_expr_with_caller_stops_for_test(
            In::new(&mut input, &mut recover, &mut output),
            super::super::operator::stops_for(TokenKind::RParen),
            0,
            0,
        )
        .expect("accepted PathSegment Type");
        let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) = exit
        else {
            panic!("close remains pending: {source:?}")
        };
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(green.to_string(), "A::@", "{source:?}");
        assert_eq!(
            records,
            [expected_type_path_segment_recovery(
                0,
                RecoveryKind::Error,
                3..4
            )]
        );
        assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::RParen));
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            leading_text,
            "{source:?}"
        );
    }

    for source in ["A::@\nB", "A::@\r\nB", "A::@ \nB", "A::@ \r\nB"] {
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), "A::@", "{source:?}");
        assert_eq!(
            records,
            [expected_type_path_segment_recovery(
                0,
                RecoveryKind::Error,
                3..4
            )]
        );
        let Some(Err(Either::Left(item))) = exit else {
            panic!("shallow newline Item remains pending: {source:?}")
        };
        assert_eq!(item.payload_view().spelling(), Some("B"), "{source:?}");
        assert!(item.leading_view().has_ordinary_newline(), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let path = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypePathTail)
            .expect("shallow PathTail");
        assert!(!path.descendants_with_tokens().any(|element| {
            element
                .into_token()
                .is_some_and(|token| token.kind() == SyntaxKind::Identifier && token.text() == "B")
        }));
    }

    let (green, _, records) = run_type_with_recoveries("A::::B", None);
    assert_eq!(green.to_string(), "A::::B");
    assert_eq!(
        records,
        [expected_type_path_segment_recovery(
            0,
            RecoveryKind::Missing,
            3..3
        )]
    );
}

#[test]
fn type_path_segment_frozen_mismatch_preserves_the_diagnostic_cursor_and_slot() {
    let mut mismatched = expected_type_path_segment_recovery(7, RecoveryKind::Error, 3..4);
    mismatched.site.range = 3..5;
    Arc::make_mut(&mut mismatched.unexpected)[0] = UnexpectedSyntax::Token {
        range: 3..5,
        category: UnexpectedCategory::OtherCharacter,
    };
    Arc::make_mut(&mut mismatched.expectations)[0].range = 3..5;
    let operators = OperatorTable::empty();
    let mut input = "A::@";
    let mut recover = Recover::new(&operators);
    let frozen = [mismatched];
    let mut output = GreenNodeBuilder::reconcile(&frozen);
    output.start_node(SyntaxKind::Root.into());
    let before_slots = output.recovery_slot_count();
    let before_diagnostics = output.diagnostic_position();
    assert_eq!(before_slots, 0);
    assert_eq!(before_diagnostics, (Some(8), 0));
    let mismatch = catch_unwind(AssertUnwindSafe(|| {
        let _ = super::super::type_expr::type_expr(In::new(&mut input, &mut recover, &mut output));
    }));
    assert!(mismatch.is_err());
    assert_eq!(output.recovery_slot_count(), before_slots);
    assert_eq!(output.diagnostic_position(), before_diagnostics);
    drop(output);
}

#[test]
fn rb_t_path_segment_rejected_retry_seal_preserves_successor_vector() {
    let operators = OperatorTable::empty();
    let frozen = [expected_type_path_segment_recovery(
        7,
        RecoveryKind::Error,
        3..4,
    )];

    for source in ["A::@ with", "A::@/*x*/ with"] {
        let mut candidate_input = source;
        let mut candidate_recover = Recover::new(&operators);
        let candidate_mark = candidate_recover.mark();
        let candidate_operators = std::ptr::eq(candidate_recover.operators(), &operators);
        let mut candidate_output = GreenNodeBuilder::reconcile(&frozen);
        candidate_output.start_node(SyntaxKind::Root.into());
        seed_identifier(&mut candidate_output);
        let (primary, primary_origin, primary_line) =
            super::super::type_expr::type_nud_item_normalized(
                In::new(
                    &mut candidate_input,
                    &mut candidate_recover,
                    &mut candidate_output,
                ),
                0,
                LineEntry::InLine,
                None,
            );
        let continuation_entry = super::super::driver::suffix_marker(In::new(
            &mut candidate_input,
            &mut candidate_recover,
            &mut candidate_output,
        ));
        let (candidate_exit, primary_found) = super::super::type_expr::
            required_type_expr_with_caller_stops_and_outer_boundary_normalized(
                In::new(
                    &mut candidate_input,
                    &mut candidate_recover,
                    &mut candidate_output,
                ),
                primary,
                0,
                0,
                super::super::type_expr::TypeOuterBoundary::WITH,
                primary_origin,
                primary_line,
                None,
            );
        let candidate_origin = super::super::driver::advanced_origin(
            primary_origin,
            continuation_entry,
            In::new(
                &mut candidate_input,
                &mut candidate_recover,
                &mut candidate_output,
            ),
        );
        let NormalizedExit::Complete(Err(Either::Left(candidate_item)), candidate_line) =
            candidate_exit
        else {
            panic!("outer WITH remains pending: {source:?}")
        };
        assert!(primary_found, "{source:?}");
        let candidate_slots = candidate_output.recovery_slot_count();
        let candidate_diagnostics = candidate_output.diagnostic_position();
        candidate_output.finish_node();
        let (candidate_green, candidate_records) = candidate_output.finish_with_recoveries();

        let pending_source = &source[4..];
        let (control_item, control_origin, control_line, control_input, control_mark, control_ops) =
            scan_type_item_control(pending_source, 4, &operators);
        let mut control_output = GreenNodeBuilder::reconcile(&frozen);
        control_output.start_node(SyntaxKind::Root.into());
        seed_identifier(&mut control_output);
        control_output.start_node(SyntaxKind::TypeExpression.into());
        control_output.token(SyntaxKind::Identifier.into(), "A");
        control_output.start_node(SyntaxKind::TypePathTail.into());
        control_output.token(SyntaxKind::ColonColon.into(), "::");
        control_output.start_node(SyntaxKind::Error.into());
        control_output.token(SyntaxKind::Unknown.into(), "@");
        control_output.finish_node();
        commit_record_draft(&mut control_output, &frozen[0]);
        control_output.finish_node();
        control_output.finish_node();
        let control_slots = control_output.recovery_slot_count();
        let control_diagnostics = control_output.diagnostic_position();
        control_output.finish_node();
        let (control_green, control_records) = control_output.finish_with_recoveries();

        assert_eq!(candidate_green, control_green, "{source:?}");
        assert_eq!(candidate_records, control_records, "{source:?}");
        assert_eq!(candidate_records, frozen, "{source:?}");
        assert_eq!(candidate_slots, control_slots, "{source:?}");
        assert_eq!(candidate_slots, 1, "{source:?}");
        assert_eq!(candidate_diagnostics, control_diagnostics, "{source:?}");
        assert_eq!(candidate_diagnostics, (Some(8), 1), "{source:?}");
        assert_eq!(candidate_input, control_input, "{source:?}");
        assert_eq!(candidate_input, "", "{source:?}");
        assert_eq!(candidate_item, control_item, "{source:?}");
        assert_eq!(candidate_item.payload_view().spelling(), Some("with"));
        assert_eq!(candidate_origin, control_origin, "{source:?}");
        assert_eq!(candidate_line, control_line, "{source:?}");
        assert_eq!(candidate_line, LineEntry::InLine, "{source:?}");
        assert_eq!(candidate_mark, control_mark, "{source:?}");
        assert_eq!(candidate_mark, ());
        assert!(candidate_operators && control_ops, "{source:?}");
    }
}

#[test]
fn type_arrow_tail_recovers_its_mandatory_rhs() {
    for (source, recovery) in [("A->", SyntaxKind::Missing), ("A->@B", SyntaxKind::Error)] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let arrow = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
            .expect("type arrow tail");
        assert_eq!(
            arrow
                .children()
                .filter(|node| node.kind() == recovery)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("A->\n");
    assert_eq!(green.to_string(), "A->\n");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let arrow = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
        .expect("type arrow tail");
    assert_eq!(
        arrow
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Arrow, "->".to_owned()),
            (SyntaxKind::Newline, "\n".to_owned()),
        ]
    );
}

#[test]
fn type_arrow_rhs_publishes_fresh_and_frozen_extended_error_records() {
    let source = "A ->@ B";
    let expected = expected_type_expression_error(
        0,
        TypeRole::ArrowRhs,
        4..6,
        Arc::from([UnexpectedSyntax::Token {
            range: 4..6,
            category: UnexpectedCategory::OtherCharacter,
        }]),
    );
    let (green, exit, records) = run_type_with_recoveries(source, None);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(records, [expected.clone()]);

    let arrow = SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
        .expect("Arrow tail");
    let error = arrow
        .children()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("Arrow-RHS Error");
    assert_eq!(error.text(), "@");
    assert_eq!(
        usize::from(error.text_range().start())..usize::from(error.text_range().end()),
        4..5
    );
    let rhs_expression = arrow
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeExpression)
        .expect("retried Arrow RHS expression");
    assert_eq!(rhs_expression.text(), " B");
    let retry_space = rhs_expression
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| {
            let range =
                usize::from(token.text_range().start())..usize::from(token.text_range().end());
            token.kind() == SyntaxKind::Whitespace && range == (5..6)
        })
        .expect("retry-owned Arrow RHS space");
    assert_eq!(retry_space.text(), " ");
    assert!(
        retry_space
            .parent_ancestors()
            .any(|ancestor| ancestor == rhs_expression)
    );
    assert!(
        !retry_space
            .parent_ancestors()
            .any(|ancestor| ancestor == error)
    );
    let rhs = rhs_expression
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::Identifier && token.text() == "B")
        .expect("retried Arrow RHS");
    assert_eq!(
        usize::from(rhs.text_range().start())..usize::from(rhs.text_range().end()),
        6..7
    );
    assert!(
        rhs.parent_ancestors()
            .any(|ancestor| ancestor == rhs_expression)
    );

    let frozen_expected = expected_type_expression_error(
        7,
        TypeRole::ArrowRhs,
        4..6,
        Arc::from([UnexpectedSyntax::Token {
            range: 4..6,
            category: UnexpectedCategory::OtherCharacter,
        }]),
    );
    let (frozen_green, frozen_exit, frozen_records) =
        run_type_with_recoveries(source, Some(std::slice::from_ref(&frozen_expected)));
    assert_eq!(frozen_green, green);
    assert!(matches!(frozen_exit, Some(Err(Either::Right(_)))));
    assert_eq!(frozen_records, [frozen_expected]);
}

#[test]
fn type_arrow_rhs_shifted_origin_keeps_local_cst_and_global_recovery_extent() {
    let source = "A ->@ B";
    let item_origin = 15;
    let expected = expected_type_expression_error(
        0,
        TypeRole::ArrowRhs,
        19..21,
        Arc::from([UnexpectedSyntax::Token {
            range: 19..21,
            category: UnexpectedCategory::OtherCharacter,
        }]),
    );
    let (green, exit, primary_found, remainder, records) =
        run_required_type_with_recoveries(source, item_origin, LineEntry::InLine, None, None);

    assert!(primary_found);
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
    ));
    assert_eq!(remainder, "");
    assert_eq!(green.to_string(), source);
    assert_eq!(records, [expected]);

    let root = SyntaxNode::new_root(green);
    let arrow = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
        .expect("shifted Arrow tail");
    let error = arrow
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("shifted Arrow-RHS Error");
    assert_eq!(error.text(), "@");
    assert_eq!(
        usize::from(error.text_range().start())..usize::from(error.text_range().end()),
        4..5,
    );
    let rhs_expression = arrow
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeExpression)
        .expect("shifted retried Arrow RHS expression");
    let retry_space = rhs_expression
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| {
            let range =
                usize::from(token.text_range().start())..usize::from(token.text_range().end());
            token.kind() == SyntaxKind::Whitespace && range == (5..6)
        })
        .expect("shifted retry-owned Arrow RHS space");
    assert_eq!(retry_space.text(), " ");
    assert!(
        retry_space
            .parent_ancestors()
            .any(|ancestor| ancestor == rhs_expression)
    );
    assert!(
        !retry_space
            .parent_ancestors()
            .any(|ancestor| ancestor == error)
    );
    let rhs = rhs_expression
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::Identifier && token.text() == "B")
        .expect("shifted Arrow RHS");
    assert_eq!(
        usize::from(rhs.text_range().start())..usize::from(rhs.text_range().end()),
        6..7,
    );
    assert!(
        rhs.parent_ancestors()
            .any(|ancestor| ancestor == rhs_expression)
    );

    assert_eq!(item_origin + 4..item_origin + 5, 19..20);
    assert_eq!(item_origin + 5..item_origin + 6, 20..21);
    assert_eq!(item_origin + 6..item_origin + 7, 21..22);
}

#[test]
fn type_arrow_rhs_frozen_mismatch_preserves_the_diagnostic_cursor_and_slot() {
    let source = "A ->@ B";
    let mut mismatched = expected_type_expression_error(
        7,
        TypeRole::ArrowRhs,
        4..6,
        Arc::from([UnexpectedSyntax::Token {
            range: 4..6,
            category: UnexpectedCategory::OtherCharacter,
        }]),
    );
    mismatched.site.range = 4..5;
    Arc::make_mut(&mut mismatched.unexpected)[0] = UnexpectedSyntax::Token {
        range: 4..5,
        category: UnexpectedCategory::OtherCharacter,
    };
    Arc::make_mut(&mut mismatched.expectations)[0].range = 4..5;
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let frozen = [mismatched];
    let mut output = GreenNodeBuilder::reconcile(&frozen);
    output.start_node(SyntaxKind::Root.into());
    let before_diagnostics = output.diagnostic_position();
    let before_slots = output.recovery_slot_count();
    assert_eq!(before_diagnostics, (Some(8), 0));
    assert_eq!(before_slots, 0);
    let mismatch = catch_unwind(AssertUnwindSafe(|| {
        let _ = super::super::type_expr::type_expr(In::new(&mut input, &mut recover, &mut output));
    }));
    assert!(mismatch.is_err());
    assert_eq!(output.diagnostic_position(), before_diagnostics);
    assert_eq!(output.recovery_slot_count(), before_slots);
    drop(output);
}

#[test]
fn type_arrow_rhs_record_extension_obeys_retry_leading_eligibility() {
    for (source, error_text, error_range, record_range, rhs_start) in [
        ("A ->@B", "@", 4..5, 4..5, Some(5)),
        ("A ->@ . B", "@ .", 4..7, 4..8, Some(8)),
        ("A ->@   B", "@", 4..5, 4..8, Some(8)),
        ("A ->@/*c*/ B", "@", 4..5, 4..11, Some(11)),
        ("A ->@\n  B", "@", 4..5, 4..5, None),
        ("A ->@\r\n  B", "@", 4..5, 4..5, None),
        ("A ->@", "@", 4..5, 4..5, None),
    ] {
        let expected = expected_type_expression_error(
            0,
            TypeRole::ArrowRhs,
            record_range.clone(),
            Arc::from([UnexpectedSyntax::Token {
                range: record_range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }]),
        );
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(records, [expected], "{source:?}");
        let root = SyntaxNode::new_root(green);
        let error = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("Arrow-RHS Error");
        assert_eq!(error.text(), error_text, "{source:?}");
        assert_eq!(
            usize::from(error.text_range().start())..usize::from(error.text_range().end()),
            error_range,
            "{source:?}"
        );
        if error_text == "@ ." {
            assert_eq!(
                error
                    .children_with_tokens()
                    .filter_map(|element| element.into_token())
                    .map(|token| (token.kind(), token.text().to_owned()))
                    .collect::<Vec<_>>(),
                [
                    (SyntaxKind::Unknown, "@".to_owned()),
                    (SyntaxKind::Whitespace, " ".to_owned()),
                    (SyntaxKind::Dot, ".".to_owned()),
                ],
                "{source:?}"
            );
        }
        if let Some(rhs_start) = rhs_start {
            let rhs = root
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::Identifier && token.text() == "B")
                .expect("retried Arrow RHS");
            assert_eq!(
                usize::from(rhs.text_range().start()),
                rhs_start,
                "{source:?}"
            );
        }
    }
}

#[test]
fn type_arrow_rhs_preserves_pending_boundaries_after_error() {
    let operators = OperatorTable::empty();
    for (source, error_text, error_range) in [("A ->@ )", "@", 4..5), ("A ->@ . )", "@ .", 4..7)] {
        let expected = expected_type_expression_error(
            0,
            TypeRole::ArrowRhs,
            error_range.clone(),
            Arc::from([UnexpectedSyntax::Token {
                range: error_range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }]),
        );
        let mut input = source;
        let mut recover = Recover::new(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (exit, successor_origin) =
            super::super::type_expr::type_expr_with_caller_stops_for_test(
                In::new(&mut input, &mut recover, &mut output),
                super::super::operator::stops_for(TokenKind::RParen),
                0,
                0,
            )
            .expect("accepted Arrow Type");
        let NormalizedExit::Complete(Err(Either::Left(item)), line_entry) = exit else {
            panic!("right parenthesis must remain pending: {source:?}")
        };
        let slots = output.recovery_slot_count();
        let diagnostics = output.diagnostic_position();
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();

        let pending_source = &source[error_range.end..];
        let (control, control_origin, control_line, control_input, mark, same_operators) =
            scan_type_item_control(pending_source, error_range.end, &operators);
        assert_eq!(green.to_string(), &source[..error_range.end], "{source:?}");
        assert_eq!(records, [expected], "{source:?}");
        assert_eq!(
            SyntaxNode::new_root(green)
                .descendants()
                .find(|node| node.kind() == SyntaxKind::Error)
                .expect("Arrow-RHS Error")
                .text(),
            error_text,
            "{source:?}"
        );
        assert_eq!(item, control, "{source:?}");
        assert_eq!(successor_origin, control_origin, "{source:?}");
        assert_eq!(line_entry, control_line, "{source:?}");
        assert_eq!(input, control_input, "{source:?}");
        assert_eq!(mark, ());
        assert!(same_operators);
        assert_eq!(slots, 1);
        assert_eq!(diagnostics, (Some(1), 0));
    }
}

#[test]
fn type_arrow_rhs_preserves_real_with_outer_boundaries_before_and_after_error() {
    let operators = OperatorTable::empty();
    for (source, emitted, pending_start, error_range) in [
        ("A -> with", "A ->", 4, None),
        ("A ->@ with", "A ->@", 5, Some(4..5)),
    ] {
        let expected = match &error_range {
            Some(range) => expected_type_expression_error(
                0,
                TypeRole::ArrowRhs,
                range.clone(),
                Arc::from([UnexpectedSyntax::Token {
                    range: range.clone(),
                    category: UnexpectedCategory::OtherCharacter,
                }]),
            ),
            None => expected_type_expression_missing(0, TypeRole::ArrowRhs, pending_start),
        };
        let (green, exit, primary_found, successor_origin, remainder, records, slots, diagnostics) =
            run_required_type_with_outer_boundary_and_recoveries(
                source,
                super::super::type_expr::TypeOuterBoundary::WITH,
                false,
                None,
            );
        let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) = exit
        else {
            panic!("WITH must remain pending after Arrow: {source:?}")
        };
        let (control, control_origin, control_line, control_remainder, mark, same_operators) =
            scan_type_item_control(&source[pending_start..], pending_start, &operators);
        assert!(primary_found, "{source:?}");
        assert_eq!(green.to_string(), emitted, "{source:?}");
        assert_eq!(records, [expected], "{source:?}");
        assert_eq!(pending, control, "{source:?}");
        assert_eq!(
            pending.payload_view().spelling(),
            Some("with"),
            "{source:?}"
        );
        assert_eq!(pending.leading_view().remaining_physical_parts(), 1);
        assert!(pending.leading_view().has_ordinary_trivia());
        assert_eq!(emit_pending_leading_text(&mut pending), " ");
        assert_eq!(successor_origin, control_origin, "{source:?}");
        assert_eq!(LineEntry::InLine, control_line, "{source:?}");
        assert_eq!(remainder, control_remainder, "{source:?}");
        assert_eq!(slots, 1, "{source:?}");
        assert_eq!(diagnostics, (Some(1), 0), "{source:?}");
        assert_eq!(mark, ());
        assert!(same_operators);
        let root = SyntaxNode::new_root(green.clone());
        match &error_range {
            Some(range) => {
                let error = root
                    .descendants()
                    .find(|node| node.kind() == SyntaxKind::Error)
                    .expect("Arrow-RHS Error");
                assert_eq!(error.text(), "@");
                assert_eq!(
                    usize::from(error.text_range().start())..usize::from(error.text_range().end()),
                    range.clone()
                );
            }
            None => assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::Missing)
                    .count(),
                1
            ),
        }

        let frozen_expected = match error_range {
            Some(range) => expected_type_expression_error(
                7,
                TypeRole::ArrowRhs,
                range.clone(),
                Arc::from([UnexpectedSyntax::Token {
                    range,
                    category: UnexpectedCategory::OtherCharacter,
                }]),
            ),
            None => expected_type_expression_missing(7, TypeRole::ArrowRhs, pending_start),
        };
        let (
            frozen_green,
            frozen_exit,
            frozen_primary_found,
            frozen_origin,
            frozen_remainder,
            frozen_records,
            frozen_slots,
            frozen_diagnostics,
        ) = run_required_type_with_outer_boundary_and_recoveries(
            source,
            super::super::type_expr::TypeOuterBoundary::WITH,
            false,
            Some(std::slice::from_ref(&frozen_expected)),
        );
        let NormalizedExit::Complete(Err(Either::Left(frozen_pending)), LineEntry::InLine) =
            frozen_exit
        else {
            panic!("frozen WITH must remain pending after Arrow: {source:?}")
        };
        assert_eq!(frozen_green, green, "{source:?}");
        assert!(frozen_primary_found, "{source:?}");
        assert_eq!(frozen_pending, control, "{source:?}");
        assert_eq!(frozen_origin, control_origin, "{source:?}");
        assert_eq!(frozen_remainder, control_remainder, "{source:?}");
        assert_eq!(frozen_records, [frozen_expected], "{source:?}");
        assert_eq!(frozen_slots, 1, "{source:?}");
        assert_eq!(frozen_diagnostics, (Some(8), 1), "{source:?}");
    }
}

#[test]
fn type_arrow_rhs_preserves_non_nud_outer_boundaries_after_error() {
    let operators = OperatorTable::empty();
    for (source, outer_boundary, pipe_lexical, pending_kind) in [
        (
            "A ->@ = Body",
            super::super::type_expr::TypeOuterBoundary::EQUALS,
            false,
            TokenKind::Equals,
        ),
        (
            "A ->@ | Body",
            super::super::type_expr::TypeOuterBoundary::PIPE,
            true,
            TokenKind::Pipe,
        ),
        (
            "A ->@ : Body",
            super::super::type_expr::TypeOuterBoundary::STRUCT_BODY,
            false,
            TokenKind::Colon,
        ),
    ] {
        let expected = expected_type_expression_error(
            0,
            TypeRole::ArrowRhs,
            4..5,
            Arc::from([UnexpectedSyntax::Token {
                range: 4..5,
                category: UnexpectedCategory::OtherCharacter,
            }]),
        );
        let (green, exit, primary_found, successor_origin, remainder, records, slots, diagnostics) =
            run_required_type_with_outer_boundary_and_recoveries(
                source,
                outer_boundary,
                pipe_lexical,
                None,
            );
        let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) = exit
        else {
            panic!("outer boundary must remain pending after Arrow Error: {source:?}")
        };
        let (control, control_origin, control_line, control_remainder, mark, same_operators) =
            scan_type_item_control_with_pipe_lexical(&source[5..], 5, &operators, pipe_lexical);

        assert!(primary_found, "{source:?}");
        assert_eq!(green.to_string(), "A ->@", "{source:?}");
        assert_eq!(records, [expected], "{source:?}");
        assert_eq!(pending, control, "{source:?}");
        assert_eq!(pending.payload_view().token_kind(), Some(pending_kind));
        assert_eq!(pending.leading_view().remaining_physical_parts(), 1);
        assert!(pending.leading_view().has_ordinary_trivia());
        assert!(!pending.leading_view().has_ordinary_newline());
        assert_eq!(emit_pending_leading_text(&mut pending), " ");
        assert_eq!(successor_origin, control_origin, "{source:?}");
        assert_eq!(successor_origin, 7, "{source:?}");
        assert_eq!(control_line, LineEntry::InLine, "{source:?}");
        assert_eq!(remainder, control_remainder, "{source:?}");
        assert_eq!(remainder, " Body", "{source:?}");
        assert_eq!(slots, 1, "{source:?}");
        assert_eq!(diagnostics, (Some(1), 0), "{source:?}");
        assert_eq!(mark, ());
        assert!(same_operators);

        let root = SyntaxNode::new_root(green);
        let error = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("Arrow-RHS Error");
        assert_eq!(error.text(), "@", "{source:?}");
        assert_eq!(
            usize::from(error.text_range().start())..usize::from(error.text_range().end()),
            4..5,
            "{source:?}",
        );
    }
}

#[test]
fn type_arrow_rhs_missing_records_use_post_emission_and_abstract_coordinates() {
    for (source, emitted, at) in [("A->", "A->", 3), ("A-> )", "A-> ", 4)] {
        let expected = expected_type_expression_missing(0, TypeRole::ArrowRhs, at);
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), emitted, "{source:?}");
        assert!(matches!(exit, Some(Err(_))), "{source:?}");
        assert_eq!(records, [expected.clone()], "{source:?}");
        let (frozen_green, _, frozen_records) =
            run_type_with_recoveries(source, Some(std::slice::from_ref(&expected)));
        assert_eq!(frozen_green, green, "{source:?}");
        assert_eq!(frozen_records, [expected], "{source:?}");
    }

    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let source = "> > A ->\n> > ```\nouter\n";
    let expected = expected_type_expression_missing(0, TypeRole::ArrowRhs, 9);
    let (green, exit, remainder, records) = run_type_normalized_with_recoveries(
        source,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
        None,
    );
    assert_eq!(green.to_string(), "> > A ->");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("Arrow RHS must preserve the abstract fence boundary")
    };
    assert!(boundary.payload_view().is_boundary());
    assert!(boundary.leading_view().has_ordinary_newline());
    assert_eq!(remainder, "> > ```\nouter\n");
    assert_eq!(records, [expected.clone()]);
    let (frozen_green, _, frozen_remainder, frozen_records) = run_type_normalized_with_recoveries(
        source,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
        Some(std::slice::from_ref(&expected)),
    );
    assert_eq!(frozen_green, green);
    assert_eq!(frozen_remainder, remainder);
    assert_eq!(frozen_records, [expected]);
}

#[test]
fn type_arrow_rhs_fenced_boundaries_and_carriers_do_not_extend_error_records() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (source, emitted, remainder, has_rhs) in [
        (
            "> > A ->@\n> > ```\nouter\n",
            "> > A ->@",
            "> > ```\nouter\n",
            false,
        ),
        (
            "> > A ->@\n> >   B\n> > ```\nouter\n",
            "> > A ->@\n> >   B",
            "> > ```\nouter\n",
            true,
        ),
    ] {
        let expected = expected_type_expression_error(
            0,
            TypeRole::ArrowRhs,
            8..9,
            Arc::from([UnexpectedSyntax::Token {
                range: 8..9,
                category: UnexpectedCategory::OtherCharacter,
            }]),
        );
        let (green, exit, actual_remainder, records) = run_type_normalized_with_recoveries(
            source,
            0,
            LineEntry::PhysicalStart,
            Some(&fence),
            None,
        );
        assert_eq!(green.to_string(), emitted, "{source:?}");
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("Arrow recovery must preserve the fence boundary: {source:?}")
        };
        assert!(boundary.payload_view().is_boundary(), "{source:?}");
        assert!(boundary.leading_view().has_ordinary_newline(), "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert_eq!(records, [expected], "{source:?}");
        let root = SyntaxNode::new_root(green);
        let error = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("Arrow-RHS Error");
        assert_eq!(error.text(), "@", "{source:?}");
        assert_eq!(
            usize::from(error.text_range().start())..usize::from(error.text_range().end()),
            8..9,
            "{source:?}"
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Identifier && token.text() == "B"),
            has_rhs,
            "{source:?}"
        );
    }
}

#[test]
fn type_arrow_rhs_valid_control_has_no_recovery() {
    let source = "A -> B";
    let (green, exit, records) = run_type_with_recoveries(source, None);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(records.is_empty());
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
    );
}

#[test]
fn type_call_t3a_missing_slots_publish_fresh_and_frozen_records_with_exact_cst_anchors() {
    let cases = [
        (
            "T(,)",
            vec![expected_type_expression_missing(
                0,
                TypeRole::CallArgument,
                2,
            )],
        ),
        ("G T(F A)", vec![expected_type_call_separator(0, 6)]),
        (
            "T(",
            vec![
                expected_type_expression_missing(0, TypeRole::CallArgument, 2),
                expected_type_call_close(1, 2),
            ],
        ),
        ("T(A", vec![expected_type_call_close(0, 3)]),
        (
            "T(A,",
            vec![
                expected_type_expression_missing(0, TypeRole::CallArgument, 4),
                expected_type_call_close(1, 4),
            ],
        ),
    ];

    for (source, expected) in cases {
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(records, expected, "{source:?}");
        let call = SyntaxNode::new_root(green.clone())
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeCallTail)
            .expect("TypeCallTail");
        assert_eq!(
            call.children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .map(|node| {
                    usize::from(node.text_range().start())..usize::from(node.text_range().end())
                })
                .collect::<Vec<_>>(),
            expected
                .iter()
                .map(|record| record.site.range.clone())
                .collect::<Vec<_>>(),
            "{source:?}",
        );

        let frozen = frozen_recovery_ids(&expected);
        let (frozen_green, frozen_exit, frozen_records) =
            run_type_with_recoveries(source, Some(&frozen));
        assert_eq!(frozen_green, green, "{source:?}");
        assert!(
            matches!(frozen_exit, Some(Err(Either::Right(_)))),
            "{source:?}"
        );
        assert_eq!(frozen_records, frozen, "{source:?}");
    }
}

#[test]
fn type_call_t3a_inherited_ml_retries_arguments_after_owned_trivia_and_close_wins() {
    for (source, separator_at, close_range) in [
        ("G T(F A)", 6, 7..8),
        ("G T(F\n  A)", 8, 9..10),
        ("G T(F\r\n  A)", 9, 10..11),
    ] {
        let expected = expected_type_call_separator(0, separator_at);
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(records, [expected.clone()], "{source:?}");
        let call = SyntaxNode::new_root(green.clone())
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeCallTail)
            .expect("TypeCallTail");
        assert_eq!(
            call.children()
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            ["F", "A"],
            "{source:?}",
        );
        let close = call
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == SyntaxKind::RParen)
            .expect("matching TypeCall close");
        assert_eq!(
            usize::from(close.text_range().start())..usize::from(close.text_range().end()),
            close_range,
            "{source:?}",
        );
        if source.contains('\n') || source.contains('\r') {
            assert!(
                call.children_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(|token| token.kind() == SyntaxKind::Newline),
                "Call owns retry newline outside Error: {source:?}",
            );
        }

        let frozen = frozen_recovery_ids(std::slice::from_ref(&expected));
        let (frozen_green, _, frozen_records) = run_type_with_recoveries(source, Some(&frozen));
        assert_eq!(frozen_green, green, "{source:?}");
        assert_eq!(frozen_records, frozen, "{source:?}");
    }

    for (source, close_range) in [
        ("G T(F\nA)", 7..8),
        ("G T(F\r\nA)", 8..9),
        ("G T(\n  F\n A)", 11..12),
        ("G T(\r\n  F\r\n A)", 13..14),
    ] {
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(records.is_empty(), "{source:?}: {records:#?}");
        let call = SyntaxNode::new_root(green.clone())
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeCallTail)
            .expect("TypeCallTail");
        assert_eq!(
            call.children()
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            ["F", "A"],
            "{source:?}",
        );
        let close = call
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == SyntaxKind::RParen)
            .expect("matching TypeCall close");
        assert_eq!(
            usize::from(close.text_range().start())..usize::from(close.text_range().end()),
            close_range,
            "{source:?}",
        );

        let frozen = [];
        let (frozen_green, frozen_exit, frozen_records) =
            run_type_with_recoveries(source, Some(&frozen));
        assert_eq!(frozen_green, green, "{source:?}");
        assert!(
            matches!(frozen_exit, Some(Err(Either::Right(_)))),
            "{source:?}",
        );
        assert!(frozen_records.is_empty(), "{source:?}");
    }

    for source in ["G T(F\n  )", "G T(F\r\n  )"] {
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(records.is_empty(), "{source:?}: {records:#?}");
    }

    for source in ["G (F A)", "G '[F A]"] {
        let (_, _, records) = run_type_with_recoveries(source, None);
        assert!(
            records.iter().all(|record| {
                record.site.role != GrammarRole::Type(TypeRole::CallArgumentSeparator)
            }),
            "non-Call owner inherited Call separator recovery: {source:?}",
        );
    }
}

#[test]
fn type_parenthesized_t4p_inherited_ml_publishes_owned_separator_and_retries() {
    let cases = [
        (
            "G (F A)",
            5,
            vec![
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::TypeExpression, 3..4),
                (SyntaxKind::Whitespace, 4..5),
                (SyntaxKind::Missing, 5..5),
                (SyntaxKind::TypeExpression, 5..6),
                (SyntaxKind::RParen, 6..7),
            ],
        ),
        (
            "G (F\n  A)",
            7,
            vec![
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::TypeExpression, 3..4),
                (SyntaxKind::Newline, 4..5),
                (SyntaxKind::Whitespace, 5..7),
                (SyntaxKind::Missing, 7..7),
                (SyntaxKind::TypeExpression, 7..8),
                (SyntaxKind::RParen, 8..9),
            ],
        ),
        (
            "G (F\r\n  A)",
            8,
            vec![
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::TypeExpression, 3..4),
                (SyntaxKind::Newline, 4..6),
                (SyntaxKind::Whitespace, 6..8),
                (SyntaxKind::Missing, 8..8),
                (SyntaxKind::TypeExpression, 8..9),
                (SyntaxKind::RParen, 9..10),
            ],
        ),
        (
            "G (F/*note*/ A)",
            13,
            vec![
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::TypeExpression, 3..4),
                (SyntaxKind::BlockComment, 4..12),
                (SyntaxKind::Whitespace, 12..13),
                (SyntaxKind::Missing, 13..13),
                (SyntaxKind::TypeExpression, 13..14),
                (SyntaxKind::RParen, 14..15),
            ],
        ),
        (
            "(A{})",
            2,
            vec![
                (SyntaxKind::LParen, 0..1),
                (SyntaxKind::TypeExpression, 1..2),
                (SyntaxKind::Missing, 2..2),
                (SyntaxKind::TypeExpression, 2..4),
                (SyntaxKind::RParen, 4..5),
            ],
        ),
    ];
    for (source, separator_at, expected_children) in cases {
        let expected = expected_parenthesized_separator(0, separator_at);
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(records, [expected.clone()], "{source:?}");
        assert_parenthesized_t4p_topology(&green, &expected_children);

        let frozen = frozen_recovery_ids(std::slice::from_ref(&expected));
        let (frozen_green, frozen_exit, frozen_records) =
            run_type_with_recoveries(source, Some(&frozen));
        assert_eq!(frozen_green, green, "{source:?}");
        assert!(
            matches!(frozen_exit, Some(Err(Either::Right(_)))),
            "{source:?}"
        );
        assert_eq!(frozen_records, frozen, "{source:?}");
    }
}

#[test]
fn type_parenthesized_t4p_standalone_and_priority_controls_publish_no_separator() {
    let cases = [
        (
            "(F A)",
            vec![],
            vec![
                (SyntaxKind::LParen, 0..1),
                (SyntaxKind::TypeExpression, 1..4),
                (SyntaxKind::RParen, 4..5),
            ],
        ),
        (
            "G (F , A)",
            vec![],
            vec![
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::TypeExpression, 3..4),
                (SyntaxKind::Whitespace, 4..5),
                (SyntaxKind::Comma, 5..6),
                (SyntaxKind::Whitespace, 6..7),
                (SyntaxKind::TypeExpression, 7..8),
                (SyntaxKind::RParen, 8..9),
            ],
        ),
        (
            "G (F; A)",
            vec![],
            vec![
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::TypeExpression, 3..4),
                (SyntaxKind::Semicolon, 4..5),
                (SyntaxKind::Whitespace, 5..6),
                (SyntaxKind::TypeExpression, 6..7),
                (SyntaxKind::RParen, 7..8),
            ],
        ),
        (
            "G (F\nA)",
            vec![],
            vec![
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::TypeExpression, 3..4),
                (SyntaxKind::Newline, 4..5),
                (SyntaxKind::TypeExpression, 5..6),
                (SyntaxKind::RParen, 6..7),
            ],
        ),
        (
            "G (F\r\nA)",
            vec![],
            vec![
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::TypeExpression, 3..4),
                (SyntaxKind::Newline, 4..6),
                (SyntaxKind::TypeExpression, 6..7),
                (SyntaxKind::RParen, 7..8),
            ],
        ),
        (
            "G (F // note\nA)",
            vec![],
            vec![
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::TypeExpression, 3..4),
                (SyntaxKind::Whitespace, 4..5),
                (SyntaxKind::LineComment, 5..12),
                (SyntaxKind::Newline, 12..13),
                (SyntaxKind::TypeExpression, 13..14),
                (SyntaxKind::RParen, 14..15),
            ],
        ),
        (
            "G (F )",
            vec![],
            vec![
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::TypeExpression, 3..4),
                (SyntaxKind::Whitespace, 4..5),
                (SyntaxKind::RParen, 5..6),
            ],
        ),
        (
            "G (F\n  )",
            vec![],
            vec![
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::TypeExpression, 3..4),
                (SyntaxKind::Newline, 4..5),
                (SyntaxKind::Whitespace, 5..7),
                (SyntaxKind::RParen, 7..8),
            ],
        ),
        (
            "G (F\r\n  )",
            vec![],
            vec![
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::TypeExpression, 3..4),
                (SyntaxKind::Newline, 4..6),
                (SyntaxKind::Whitespace, 6..8),
                (SyntaxKind::RParen, 8..9),
            ],
        ),
        (
            "G (F",
            vec![expected_parenthesized_close(0, 4)],
            vec![
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::TypeExpression, 3..4),
                (SyntaxKind::Missing, 4..4),
            ],
        ),
    ];
    for (source, expected, expected_children) in cases {
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(records, expected, "{source:?}");
        assert!(
            records.iter().all(|record| {
                record.site.role != GrammarRole::Type(TypeRole::ParenthesizedSeparator)
            }),
            "{source:?}: {records:#?}",
        );
        assert_parenthesized_t4p_topology(&green, &expected_children);

        let frozen = frozen_recovery_ids(&records);
        let (frozen_green, frozen_exit, frozen_records) =
            run_type_with_recoveries(source, Some(&frozen));
        assert_eq!(frozen_green, green, "{source:?}");
        assert!(
            matches!(frozen_exit, Some(Err(Either::Right(_)))),
            "{source:?}"
        );
        assert_eq!(frozen_records, frozen, "{source:?}");
    }
}

#[test]
fn type_parenthesized_t4p_seeded_context_phase_is_lexical_and_frozen_stable() {
    let inactive = super::super::type_expr::TypeMlContext::INACTIVE;
    let outer_active = super::super::type_expr::TypeMlContext::outer_active_for_test();
    let outer_dormant = super::super::type_expr::TypeMlContext::outer_dormant_for_test();
    let non_type_apply = super::super::type_expr::TypeMlContext::non_type_apply_active_for_test();

    for (label, context, expected) in [
        ("inactive", inactive, vec![]),
        (
            "outer-active",
            outer_active,
            vec![expected_parenthesized_separator(0, 3)],
        ),
        (
            "outer-dormant",
            outer_dormant,
            vec![expected_parenthesized_separator(0, 3)],
        ),
        ("non-TypeApply", non_type_apply, vec![]),
    ] {
        let fresh =
            run_contextual_type_snapshot("(F A)", context, 0, 0, 0, LineEntry::InLine, None, None);
        assert_eq!(fresh.green.to_string(), "sentinel(F A)", "{label}");
        assert!(
            matches!(
                fresh.exit,
                NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
            ),
            "{label}"
        );
        assert_eq!(fresh.successor_origin, 5, "{label}");
        assert_eq!(fresh.remainder, "", "{label}");
        assert_eq!(fresh.records, expected, "{label}");
        assert_eq!(fresh.slots, fresh.records.len(), "{label}");
        assert_eq!(
            fresh.diagnostics,
            (Some(u32::try_from(fresh.records.len()).unwrap()), 0),
            "{label}",
        );
        assert_eq!(fresh.mark, (), "{label}");
        assert!(fresh.same_operators, "{label}");
        assert!(
            !SyntaxNode::new_root(fresh.green.clone())
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{label}",
        );

        let frozen = frozen_recovery_ids(&fresh.records);
        let frozen_run = run_contextual_type_snapshot(
            "(F A)",
            context,
            0,
            0,
            0,
            LineEntry::InLine,
            None,
            Some(&frozen),
        );
        assert_eq!(frozen_run.green, fresh.green, "{label}");
        assert_eq!(
            frozen_run.successor_origin, fresh.successor_origin,
            "{label}"
        );
        assert_eq!(frozen_run.remainder, fresh.remainder, "{label}");
        assert_eq!(frozen_run.records, frozen, "{label}");
        assert_eq!(frozen_run.slots, frozen.len(), "{label}");
        assert_eq!(frozen_run.diagnostics.1, frozen.len(), "{label}");
        assert_eq!(frozen_run.mark, fresh.mark, "{label}");
        assert!(frozen_run.same_operators, "{label}");
    }

    let expected = expected_parenthesized_separator(7, 3);
    let (fresh_green, _, _) = run_type_with_context_and_recoveries("(F A)", outer_active, None);
    let (frozen_green, _, frozen_records) = run_type_with_context_and_recoveries(
        "(F A)",
        outer_active,
        Some(std::slice::from_ref(&expected)),
    );
    assert_eq!(frozen_green, fresh_green);
    assert_eq!(frozen_records, [expected]);

    assert_eq!(outer_active.enter_non_type_apply(), outer_active);
    assert_eq!(outer_dormant.enter_non_type_apply(), outer_active);
    assert_eq!(outer_active.dormant(), outer_dormant);

    let (_, _, standalone_records) = run_type_with_recoveries("(F A)", None);
    assert!(standalone_records.is_empty());
}

#[test]
fn type_parenthesized_t4p_rejected_probe_preserves_seeded_output_and_context() {
    let operators = OperatorTable::empty();
    for (label, context) in t4p_seeded_contexts() {
        for reconciled in [false, true] {
            let frozen = [];
            let mut input = "@";
            let mut recover = Recover::new(&operators);
            let mark = recover.mark();
            let same_operators = std::ptr::eq(recover.operators(), &operators);
            let mut output = if reconciled {
                GreenNodeBuilder::reconcile(&frozen)
            } else {
                GreenNodeBuilder::new()
            };
            output.start_node(SyntaxKind::Root.into());
            seed_identifier(&mut output);
            let before_slots = output.recovery_slot_count();
            let before_diagnostics = output.diagnostic_position();
            let exit = super::super::type_expr::type_expr_with_context_for_test(
                In::new(&mut input, &mut recover, &mut output),
                context,
                0,
            );
            assert!(exit.is_none(), "{label}, reconciled={reconciled}");
            assert_eq!(input, "@", "{label}, reconciled={reconciled}");
            assert_eq!(
                output.recovery_slot_count(),
                before_slots,
                "{label}, reconciled={reconciled}",
            );
            assert_eq!(
                output.diagnostic_position(),
                before_diagnostics,
                "{label}, reconciled={reconciled}",
            );
            assert_eq!(mark, (), "{label}, reconciled={reconciled}");
            assert!(same_operators, "{label}, reconciled={reconciled}");
            output.finish_node();
            let (green, records) = output.finish_with_recoveries();
            assert_eq!(green.to_string(), "sentinel", "{label}");
            assert!(records.is_empty(), "{label}: {records:#?}");
        }
    }
}

#[test]
fn type_parenthesized_t4p_frozen_rejection_preserves_all_seeded_cursors() {
    let operators = OperatorTable::empty();
    let mismatched = [expected_parenthesized_separator(7, 2)];
    for (label, context) in t4p_seeded_contexts() {
        let mut input = "(F";
        let mut recover = Recover::new(&operators);
        let mark = recover.mark();
        let same_operators = std::ptr::eq(recover.operators(), &operators);
        let mut output = GreenNodeBuilder::reconcile(&mismatched);
        output.start_node(SyntaxKind::Root.into());
        seed_identifier(&mut output);
        let before_slots = output.recovery_slot_count();
        let before_diagnostics = output.diagnostic_position();
        assert_eq!(before_slots, 0, "{label}");
        assert_eq!(before_diagnostics, (Some(8), 0), "{label}");
        let mismatch = catch_unwind(AssertUnwindSafe(|| {
            let _ = super::super::type_expr::type_expr_with_context_for_test(
                In::new(&mut input, &mut recover, &mut output),
                context,
                0,
            )
            .expect("EOF fixture starts with a TypeExpression");
        }));
        assert!(mismatch.is_err(), "{label}");
        assert_eq!(input, "", "{label}");
        assert_eq!(output.recovery_slot_count(), before_slots, "{label}");
        assert_eq!(output.diagnostic_position(), before_diagnostics, "{label}");
        assert_eq!(mark, (), "{label}");
        assert!(same_operators, "{label}");
        drop(output);
    }
}

#[test]
fn type_parenthesized_t4p_seeded_eof_and_local_close_exits_are_fresh_frozen_stable() {
    for (label, context) in t4p_seeded_contexts() {
        for (source, expected) in [
            ("(F)", vec![]),
            ("(F", vec![expected_parenthesized_close(0, 2)]),
        ] {
            let fresh = run_contextual_type_snapshot(
                source,
                context,
                0,
                0,
                0,
                LineEntry::InLine,
                None,
                None,
            );
            assert_eq!(
                fresh.green.to_string(),
                format!("sentinel{source}"),
                "{label}"
            );
            assert!(
                matches!(
                    fresh.exit,
                    NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
                ),
                "{label}, {source:?}"
            );
            assert_eq!(fresh.successor_origin, source.len(), "{label}, {source:?}");
            assert_eq!(fresh.remainder, "", "{label}, {source:?}");
            assert_eq!(fresh.records, expected, "{label}, {source:?}");
            assert_eq!(fresh.slots, fresh.records.len(), "{label}, {source:?}");
            assert_eq!(
                fresh.diagnostics,
                (Some(u32::try_from(fresh.records.len()).unwrap()), 0),
                "{label}, {source:?}",
            );
            assert_eq!(fresh.mark, (), "{label}, {source:?}");
            assert!(fresh.same_operators, "{label}, {source:?}");
            assert!(
                fresh.records.iter().all(|record| {
                    record.site.role != GrammarRole::Type(TypeRole::ParenthesizedSeparator)
                }),
                "{label}, {source:?}: {:#?}",
                fresh.records
            );

            let frozen = frozen_recovery_ids(&fresh.records);
            let frozen_run = run_contextual_type_snapshot(
                source,
                context,
                0,
                0,
                0,
                LineEntry::InLine,
                None,
                Some(&frozen),
            );
            assert_eq!(frozen_run.green, fresh.green, "{label}, {source:?}");
            assert_eq!(
                frozen_run.successor_origin, fresh.successor_origin,
                "{label}"
            );
            assert_eq!(frozen_run.remainder, fresh.remainder, "{label}");
            assert_eq!(frozen_run.records, frozen, "{label}, {source:?}");
            assert_eq!(frozen_run.slots, frozen.len(), "{label}, {source:?}");
            assert_eq!(frozen_run.diagnostics.1, frozen.len(), "{label}");
            assert_eq!(frozen_run.mark, fresh.mark, "{label}");
            assert!(frozen_run.same_operators, "{label}");
        }
    }
}

#[test]
fn type_parenthesized_t4p_seeded_owned_boundaries_preserve_pending_item_frontiers() {
    let outer_rbrace = super::super::type_expr::with_type_outer_close(0, TokenKind::RBrace);
    for (context_label, context) in t4p_seeded_contexts() {
        for (boundary_label, source, caller_stops, outer_closes, spelling, token_kind) in [
            (
                "caller",
                "(F with tail",
                super::super::operator::STOP_WITH,
                0,
                Some("with"),
                None,
            ),
            (
                "outer-close",
                "(F }tail",
                0,
                outer_rbrace,
                Some("}"),
                Some(TokenKind::RBrace),
            ),
        ] {
            let expected = expected_parenthesized_close(0, 3);
            let fresh = run_contextual_type_snapshot(
                source,
                context,
                caller_stops,
                outer_closes,
                0,
                LineEntry::InLine,
                None,
                None,
            );
            assert_eq!(
                fresh.green.to_string(),
                "sentinel(F ",
                "{context_label}, {boundary_label}",
            );
            let NormalizedExit::Complete(Err(Either::Left(mut pending)), line_entry) = fresh.exit
            else {
                panic!("pending boundary: {context_label}, {boundary_label}")
            };
            let control_source = &source[2..];
            let (
                mut control,
                control_origin,
                control_line,
                control_remainder,
                mark,
                same_operators,
            ) = scan_type_item_control(control_source, 2, &OperatorTable::empty());
            assert_eq!(emit_pending_leading_text(&mut control), " ");
            assert_eq!(pending, control, "{context_label}, {boundary_label}");
            assert_eq!(
                fresh.successor_origin, control_origin,
                "{context_label}, {boundary_label}"
            );
            assert_eq!(
                fresh.remainder, control_remainder,
                "{context_label}, {boundary_label}"
            );
            assert_eq!(
                line_entry, control_line,
                "{context_label}, {boundary_label}"
            );
            assert_eq!(pending.leading_view().remaining_physical_parts(), 0);
            assert!(!pending.leading_view().has_ordinary_trivia());
            assert!(!pending.leading_view().has_ordinary_newline());
            assert_eq!(pending.payload_view().spelling(), spelling);
            if let Some(token_kind) = token_kind {
                assert_eq!(pending.payload_view().token_kind(), Some(token_kind));
            }
            assert_eq!(emit_pending_leading_text(&mut pending), "");
            assert_eq!(fresh.records, [expected.clone()]);
            assert_eq!(fresh.slots, 1);
            assert_eq!(fresh.diagnostics, (Some(1), 0));
            assert_eq!(fresh.mark, ());
            assert!(fresh.same_operators);
            assert_eq!(mark, ());
            assert!(same_operators);
            assert!(fresh.records.iter().all(|record| {
                record.site.role != GrammarRole::Type(TypeRole::ParenthesizedSeparator)
            }));

            let frozen = frozen_recovery_ids(std::slice::from_ref(&expected));
            let frozen_run = run_contextual_type_snapshot(
                source,
                context,
                caller_stops,
                outer_closes,
                0,
                LineEntry::InLine,
                None,
                Some(&frozen),
            );
            assert_eq!(
                frozen_run.green, fresh.green,
                "{context_label}, {boundary_label}"
            );
            let NormalizedExit::Complete(Err(Either::Left(frozen_pending)), frozen_line) =
                frozen_run.exit
            else {
                panic!("frozen pending boundary: {context_label}, {boundary_label}")
            };
            assert_eq!(frozen_pending, control, "{context_label}, {boundary_label}");
            assert_eq!(
                frozen_line, control_line,
                "{context_label}, {boundary_label}"
            );
            assert_eq!(frozen_run.successor_origin, control_origin);
            assert_eq!(frozen_run.remainder, control_remainder);
            assert_eq!(frozen_run.records, frozen);
            assert_eq!(frozen_run.slots, 1);
            assert_eq!(frozen_run.diagnostics, (Some(8), 1));
            assert_eq!(frozen_run.mark, ());
            assert!(frozen_run.same_operators);
        }
    }
}

#[test]
fn type_parenthesized_t4p_seeded_abstract_boundary_is_unconsumed_fresh_and_frozen() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let source = "> > (F\n> > ```\nouter";
    for (label, context) in t4p_seeded_contexts() {
        let expected = expected_parenthesized_close(0, 6);
        let fresh = run_contextual_type_snapshot(
            source,
            context,
            0,
            0,
            0,
            LineEntry::PhysicalStart,
            Some(&fence),
            None,
        );
        assert_eq!(fresh.green.to_string(), "sentinel> > (F", "{label}");
        let NormalizedExit::Complete(Err(Either::Left(pending)), LineEntry::PhysicalStart) =
            fresh.exit
        else {
            panic!("abstract boundary remains pending: {label}")
        };
        assert!(pending.payload_view().is_boundary(), "{label}");
        assert!(pending.leading_view().has_ordinary_newline(), "{label}");
        assert_eq!(fresh.remainder, "> > ```\nouter", "{label}");
        assert_eq!(fresh.records, [expected.clone()], "{label}");
        assert_eq!(fresh.slots, 1, "{label}");
        assert_eq!(fresh.diagnostics, (Some(1), 0), "{label}");
        assert_eq!(fresh.mark, (), "{label}");
        assert!(fresh.same_operators, "{label}");
        assert!(fresh.records.iter().all(|record| {
            record.site.role != GrammarRole::Type(TypeRole::ParenthesizedSeparator)
        }));

        let frozen = frozen_recovery_ids(std::slice::from_ref(&expected));
        let frozen_run = run_contextual_type_snapshot(
            source,
            context,
            0,
            0,
            0,
            LineEntry::PhysicalStart,
            Some(&fence),
            Some(&frozen),
        );
        assert_eq!(frozen_run.green, fresh.green, "{label}");
        let NormalizedExit::Complete(Err(Either::Left(frozen_pending)), LineEntry::PhysicalStart) =
            frozen_run.exit
        else {
            panic!("frozen abstract boundary remains pending: {label}")
        };
        assert_eq!(frozen_pending, pending, "{label}");
        assert_eq!(
            frozen_run.successor_origin, fresh.successor_origin,
            "{label}"
        );
        assert_eq!(frozen_run.remainder, fresh.remainder, "{label}");
        assert_eq!(frozen_run.records, frozen, "{label}");
        assert_eq!(frozen_run.slots, frozen.len(), "{label}");
        assert_eq!(frozen_run.diagnostics, (Some(8), 1), "{label}");
        assert_eq!(frozen_run.mark, fresh.mark, "{label}");
        assert!(frozen_run.same_operators, "{label}");
    }
}

#[test]
fn type_parenthesized_t4p_provenance_routes_each_delimited_owner_record() {
    for (source, separator_at) in [
        ("G ((F A))", 6),
        ("G T((F A))", 7),
        ("G T[(F A)]->U", 7),
        ("G {x: (F A)}", 9),
        ("G :{Tag (F A)}", 11),
        ("G '[(F A)]", 7),
    ] {
        let expected = expected_parenthesized_separator(0, separator_at);
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(records, [expected.clone()], "{source:?}");
        assert!(records.iter().all(|record| {
            !matches!(
                record.site.role,
                GrammarRole::Type(
                    TypeRole::CallArgumentSeparator
                        | TypeRole::BracketRowSeparator
                        | TypeRole::EffectRowSeparator
                )
            )
        }));

        let frozen = frozen_recovery_ids(std::slice::from_ref(&expected));
        let (frozen_green, _, frozen_records) = run_type_with_recoveries(source, Some(&frozen));
        assert_eq!(frozen_green, green, "{source:?}");
        assert_eq!(frozen_records, frozen, "{source:?}");
    }

    let (green, exit, records) = run_type_with_recoveries("G T(F A)", None);
    assert_eq!(green.to_string(), "G T(F A)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(records, [expected_type_call_separator(0, 6)]);

    for (source, expected) in [
        ("G '[F A]", vec![pe_recovery::separator(0, true, 6)]),
        ("G T[F A]->U", vec![]),
    ] {
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(records, expected, "{source:?}");
        assert!(
            records.iter().all(|record| {
                !matches!(
                    record.site.role,
                    GrammarRole::Type(TypeRole::BracketRowSeparator)
                )
            }),
            "{source:?}: {records:#?}"
        );
        let top = top_type_expression(&green);
        assert_direct_children_topology(
            &top,
            &[
                (SyntaxKind::Identifier, 0..1),
                (SyntaxKind::TypeApplyArgument, 1..source.len()),
            ],
        );
        let apply = top
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeApplyArgument)
            .expect("outer TypeApply argument");
        assert_direct_children_topology(
            &apply,
            &[
                (SyntaxKind::Whitespace, 1..2),
                (SyntaxKind::TypeExpression, 2..source.len()),
            ],
        );
        let argument = apply
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeExpression)
            .expect("complete outer TypeApply argument");
        match source {
            "G '[F A]" => {
                assert_direct_children_topology(&argument, &[(SyntaxKind::EffectRowType, 2..8)]);
                let row = argument
                    .children()
                    .find(|node| node.kind() == SyntaxKind::EffectRowType)
                    .expect("effect row argument");
                assert_direct_children_topology(
                    &row,
                    &[
                        (SyntaxKind::Apostrophe, 2..3),
                        (SyntaxKind::LBracket, 3..4),
                        (SyntaxKind::TypeExpression, 4..5),
                        (SyntaxKind::Whitespace, 5..6),
                        (SyntaxKind::Missing, 6..6),
                        (SyntaxKind::TypeExpression, 6..7),
                        (SyntaxKind::RBracket, 7..8),
                    ],
                );
            }
            "G T[F A]->U" => {
                assert_direct_children_topology(
                    &argument,
                    &[
                        (SyntaxKind::Identifier, 2..3),
                        (SyntaxKind::TypeArrowTail, 3..11),
                    ],
                );
                let tail = argument
                    .children()
                    .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
                    .expect("bracket-row arrow continuation");
                assert_direct_children_topology(
                    &tail,
                    &[
                        (SyntaxKind::BracketRow, 3..8),
                        (SyntaxKind::Arrow, 8..10),
                        (SyntaxKind::TypeExpression, 10..11),
                    ],
                );
                let row = tail
                    .children()
                    .find(|node| node.kind() == SyntaxKind::BracketRow)
                    .expect("bracket row");
                assert_direct_children_topology(
                    &row,
                    &[
                        (SyntaxKind::LBracket, 3..4),
                        (SyntaxKind::TypeExpression, 4..7),
                        (SyntaxKind::RBracket, 7..8),
                    ],
                );
            }
            _ => unreachable!(),
        }
        assert_eq!(
            SyntaxNode::new_root(green.clone())
                .descendants()
                .filter(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
                .count(),
            expected.len(),
            "{source:?}",
        );

        let frozen = frozen_recovery_ids(&expected);
        let (frozen_green, frozen_exit, frozen_records) =
            run_type_with_recoveries(source, Some(&frozen));
        assert_eq!(frozen_green, green, "{source:?}");
        assert!(
            matches!(frozen_exit, Some(Err(Either::Right(_)))),
            "{source:?}",
        );
        assert_eq!(frozen_records, frozen, "{source:?}");
    }
}

#[test]
fn type_parenthesized_t4p_dormant_provenance_crosses_forall_without_sibling_records() {
    let context = super::super::type_expr::TypeMlContext::outer_dormant_for_test();
    let expected = expected_parenthesized_separator(0, 11);
    let (green, exit, records) =
        run_type_with_context_and_recoveries("for 'a: (F A)", context, None);
    assert_eq!(green.to_string(), "for 'a: (F A)");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
    ));
    assert_eq!(records, [expected.clone()]);
    assert!(records.iter().all(|record| {
        !matches!(
            record.site.role,
            GrammarRole::Type(
                TypeRole::CallArgumentSeparator
                    | TypeRole::EffectRowSeparator
                    | TypeRole::BracketRowSeparator
            )
        )
    }));

    let frozen = frozen_recovery_ids(std::slice::from_ref(&expected));
    let (frozen_green, frozen_exit, frozen_records) =
        run_type_with_context_and_recoveries("for 'a: (F A)", context, Some(&frozen));
    assert_eq!(frozen_green, green);
    assert!(matches!(
        frozen_exit,
        NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
    ));
    assert_eq!(frozen_records, frozen);
}

#[test]
fn type_parenthesized_t4p_lexical_sequences_do_not_leak_context_between_attempts() {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());

    let mut rejected_input = "G @";
    let (rejected_exit, rejected_origin) =
        super::super::type_expr::type_expr_with_context_for_test(
            In::new(&mut rejected_input, &mut recover, &mut output),
            super::super::type_expr::TypeMlContext::INACTIVE,
            0,
        )
        .expect("G remains an accepted Type when its Apply probe rejects");
    let NormalizedExit::Complete(Err(Either::Left(mut rejected)), LineEntry::InLine) =
        rejected_exit
    else {
        panic!("rejected TypeApply argument remains pending")
    };
    assert_eq!(rejected.payload_view().spelling(), Some("@"));
    assert_eq!(emit_pending_leading_text(&mut rejected), " ");
    assert_eq!(rejected_input, "");
    assert_eq!(rejected_origin, 3);
    assert_eq!(output.recovery_slot_count(), 0);
    assert_eq!(output.diagnostic_position(), (Some(0), 0));

    let mut standalone_input = "(F A)";
    let (mut standalone_exit, standalone_origin) =
        super::super::type_expr::type_expr_with_context_for_test(
            In::new(&mut standalone_input, &mut recover, &mut output),
            super::super::type_expr::TypeMlContext::INACTIVE,
            3,
        )
        .expect("standalone Parenthesized Type after rejected Apply probe");
    if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut standalone_exit {
        emit_end(&mut output, end);
    }
    assert_eq!(standalone_origin, 8);
    assert_eq!(standalone_input, "");
    assert_eq!(output.recovery_slot_count(), 0);
    assert_eq!(output.diagnostic_position(), (Some(0), 0));
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), "G(F A)");
    assert!(records.is_empty());

    let mut recover = Recover::new(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let outer = super::super::type_expr::TypeMlContext::outer_active_for_test();
    let mut affected_input = "(F A)";
    let (mut affected_exit, affected_origin) =
        super::super::type_expr::type_expr_with_context_for_test(
            In::new(&mut affected_input, &mut recover, &mut output),
            outer,
            0,
        )
        .expect("affected Parenthesized Type");
    if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut affected_exit {
        emit_end(&mut output, end);
    }
    assert_eq!(affected_origin, 5);
    assert_eq!(affected_input, "");
    assert_eq!(output.recovery_slot_count(), 1);
    assert_eq!(output.diagnostic_position(), (Some(1), 0));

    let mut second_standalone_input = "(F A)";
    let (mut second_exit, second_origin) =
        super::super::type_expr::type_expr_with_context_for_test(
            In::new(&mut second_standalone_input, &mut recover, &mut output),
            super::super::type_expr::TypeMlContext::INACTIVE,
            5,
        )
        .expect("standalone Parenthesized Type after affected parse");
    if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut second_exit {
        emit_end(&mut output, end);
    }
    assert_eq!(second_origin, 10);
    assert_eq!(second_standalone_input, "");
    assert_eq!(output.recovery_slot_count(), 1);
    assert_eq!(output.diagnostic_position(), (Some(1), 0));
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), "(F A)(F A)");
    assert_eq!(records, [expected_parenthesized_separator(0, 3)]);
}

#[test]
fn type_parenthesized_t4p_nested_typeapply_restores_non_typeapply_payload_phase() {
    let source = ":{Tag (G (F A)) (F A)}";
    let (green, exit, records) = run_type_with_recoveries(source, None);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(records, [expected_parenthesized_separator(0, 12)]);
    let groups = SyntaxNode::new_root(green)
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::ParenthesizedTypeGroup)
        .collect::<Vec<_>>();
    assert_eq!(groups.len(), 3);
    assert_eq!(
        groups
            .iter()
            .filter(|group| {
                group
                    .children()
                    .any(|node| node.kind() == SyntaxKind::Missing)
            })
            .count(),
        1,
    );
}

#[test]
fn type_call_t3a_missing_phase_suspends_contextual_but_preserves_caller_boundaries() {
    for (source, at) in [("T(with", 6), ("T(A with", 8), ("T(A, with", 9)] {
        let expected = [expected_type_call_close(0, at)];
        let (green, exit, primary_found, _, _, records, _, _) =
            run_required_type_with_outer_boundary_and_recoveries(
                source,
                super::super::type_expr::TypeOuterBoundary::WITH,
                false,
                None,
            );
        assert!(primary_found, "{source:?}");
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
        ));
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(records, expected, "{source:?}");
        let frozen = frozen_recovery_ids(&expected);
        let (frozen_green, frozen_exit, _, _, _, frozen_records, _, _) =
            run_required_type_with_outer_boundary_and_recoveries(
                source,
                super::super::type_expr::TypeOuterBoundary::WITH,
                false,
                Some(&frozen),
            );
        assert_eq!(frozen_green, green);
        assert_eq!(frozen_records, frozen);
        assert!(matches!(
            frozen_exit,
            NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
        ));
    }

    let operators = OperatorTable::empty();
    let active_close_stops = stops_for(TokenKind::RBracket)
        & !super::super::operator::STOP_COMMA
        & !super::super::operator::STOP_SEMICOLON;
    for (source, emitted, expected) in [
        (
            "T( ] tail",
            "T( ",
            vec![
                expected_type_expression_missing(0, TypeRole::CallArgument, 3),
                expected_type_call_close(1, 3),
            ],
        ),
        ("T(A ] tail", "T(A ", vec![expected_type_call_close(0, 4)]),
        (
            "T(A, ] tail",
            "T(A, ",
            vec![
                expected_type_expression_missing(0, TypeRole::CallArgument, 5),
                expected_type_call_close(1, 5),
            ],
        ),
    ] {
        let mut input = source;
        let mut recover = Recover::new(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (exit, _) = super::super::type_expr::type_expr_with_caller_stops_for_test(
            In::new(&mut input, &mut recover, &mut output),
            active_close_stops,
            0,
            0,
        )
        .expect("accepted TypeCall");
        let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) = exit
        else {
            panic!("caller close remains pending: {source:?}")
        };
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(green.to_string(), emitted, "{source:?}");
        assert_eq!(
            pending.payload_view().token_kind(),
            Some(TokenKind::RBracket)
        );
        assert_eq!(emit_pending_leading_text(&mut pending), "", "{source:?}");
        assert_eq!(input, " tail", "{source:?}");
        assert_eq!(records, expected, "{source:?}");
    }
}

#[test]
fn type_call_t3b_retry_keeps_contextual_names_local_and_outer_closes_pending() {
    for (source, error_range, close_at) in [("T(@ with", 2..4, 8), ("T(A,@ with", 4..6, 10)] {
        let expected = vec![
            expected_type_call_argument_error(0, error_range.clone()),
            expected_type_call_close(1, close_at),
        ];
        let (green, exit, primary_found, _, _, records, _, _) =
            run_required_type_with_outer_boundary_and_recoveries(
                source,
                super::super::type_expr::TypeOuterBoundary::WITH,
                false,
                None,
            );
        assert!(primary_found, "{source:?}");
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
        ));
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(records, expected, "{source:?}");
        let root = SyntaxNode::new_root(green.clone());
        let error = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("typed CallArgument Error");
        assert_eq!(error.text(), "@ ", "{source:?}");
        assert_eq!(
            usize::from(error.text_range().start())..usize::from(error.text_range().end()),
            error_range,
            "{source:?}",
        );

        let frozen = frozen_recovery_ids(&expected);
        let (frozen_green, frozen_exit, _, _, _, frozen_records, _, _) =
            run_required_type_with_outer_boundary_and_recoveries(
                source,
                super::super::type_expr::TypeOuterBoundary::WITH,
                false,
                Some(&frozen),
            );
        assert!(matches!(
            frozen_exit,
            NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
        ));
        assert_eq!(frozen_green, green, "{source:?}");
        assert_eq!(frozen_records, frozen, "{source:?}");
    }

    for (source, call_text, error_range, close_at) in
        [("[T(@ ]", "(@", 3..4, 4), ("[T(A,@ ]", "(A,@", 5..6, 6)]
    {
        let expected = vec![
            expected_type_call_argument_error(0, error_range.clone()),
            expected_type_call_close(1, close_at),
        ];
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(records, expected, "{source:?}");
        let root = SyntaxNode::new_root(green.clone());
        let call = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeCallTail)
            .expect("nested TypeCallTail");
        assert_eq!(call.text(), call_text, "{source:?}");
        let error = call
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("typed CallArgument Error");
        assert_eq!(error.text(), "@", "{source:?}");
        assert_eq!(
            usize::from(error.text_range().start())..usize::from(error.text_range().end()),
            error_range,
            "{source:?}",
        );

        let frozen = frozen_recovery_ids(&expected);
        let (frozen_green, frozen_exit, frozen_records) =
            run_type_with_recoveries(source, Some(&frozen));
        assert_eq!(frozen_green, green, "{source:?}");
        assert!(
            matches!(frozen_exit, Some(Err(Either::Right(_)))),
            "{source:?}",
        );
        assert_eq!(frozen_records, frozen, "{source:?}");
    }

    let operators = OperatorTable::empty();
    let active_close_stops = stops_for(TokenKind::RBracket)
        & !super::super::operator::STOP_COMMA
        & !super::super::operator::STOP_SEMICOLON;
    for (source, emitted, error_range, close_at) in [
        ("T(@ ] tail", "T(@", 2..3, 3),
        ("T(A,@ ] tail", "T(A,@", 4..5, 5),
    ] {
        let mut input = source;
        let mut recover = Recover::new(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (exit, _) = super::super::type_expr::type_expr_with_caller_stops_for_test(
            In::new(&mut input, &mut recover, &mut output),
            active_close_stops,
            0,
            0,
        )
        .expect("accepted TypeCall");
        let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) = exit
        else {
            panic!("caller close remains pending after Call error: {source:?}")
        };
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(green.to_string(), emitted, "{source:?}");
        assert_eq!(
            pending.payload_view().token_kind(),
            Some(TokenKind::RBracket),
            "{source:?}",
        );
        assert_eq!(emit_pending_leading_text(&mut pending), " ", "{source:?}");
        assert_eq!(input, " tail", "{source:?}");
        assert_eq!(
            records,
            [
                expected_type_call_argument_error(0, error_range.clone()),
                expected_type_call_close(1, close_at),
            ],
            "{source:?}"
        );
        let error = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("typed CallArgument Error");
        assert_eq!(error.text(), "@", "{source:?}");
        assert_eq!(
            usize::from(error.text_range().start())..usize::from(error.text_range().end()),
            error_range,
            "{source:?}",
        );
    }
}

#[test]
fn type_call_t3b_abstract_boundary_preserves_typed_error_and_pending_coordinate() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let source = "> > T(\n> > ```\nouter\n";
    let expected = vec![
        expected_type_expression_missing(0, TypeRole::CallArgument, 7),
        expected_type_call_close(1, 7),
    ];
    let (green, exit, remainder, records) = run_type_normalized_with_recoveries(
        source,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
        None,
    );
    assert_eq!(green.to_string(), "> > T(");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("TypeCall preserves the abstract fence boundary")
    };
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter\n");
    assert_eq!(records, expected);

    let frozen = frozen_recovery_ids(&expected);
    let (frozen_green, _, frozen_remainder, frozen_records) = run_type_normalized_with_recoveries(
        source,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
        Some(&frozen),
    );
    assert_eq!(frozen_green, green);
    assert_eq!(frozen_remainder, remainder);
    assert_eq!(frozen_records, frozen);

    let source = "> > T(@\n> > ```\nouter\n";
    let expected = vec![
        expected_type_call_argument_error(0, 6..7),
        expected_type_call_close(1, 8),
    ];
    let (green, exit, remainder, records) = run_type_normalized_with_recoveries(
        source,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
        None,
    );
    assert_eq!(green.to_string(), "> > T(@");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("TypeCall Error preserves the abstract fence boundary")
    };
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter\n");
    assert_eq!(records, expected);
    let error = SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("typed CallArgument Error");
    assert_eq!(error.text(), "@");
    assert_eq!(
        usize::from(error.text_range().start())..usize::from(error.text_range().end()),
        6..7,
    );

    let frozen = frozen_recovery_ids(&expected);
    let (frozen_green, _, frozen_remainder, frozen_records) = run_type_normalized_with_recoveries(
        source,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
        Some(&frozen),
    );
    assert_eq!(frozen_green, green);
    assert_eq!(frozen_remainder, remainder);
    assert_eq!(frozen_records, frozen);
}

#[test]
fn type_call_t3b_publishes_argument_error_and_maps_missing_records_from_shifted_origin() {
    let (green, exit, records) = run_type_with_recoveries("T(@A)", None);
    assert_eq!(green.to_string(), "T(@A)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(records, [expected_type_call_argument_error(0, 2..3)]);
    let error = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("typed CallArgument Error");
    assert_eq!(error.text(), "@");
    assert_eq!(
        error
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [(SyntaxKind::Unknown, "@".to_owned())],
    );

    let expected = vec![
        expected_type_expression_missing(0, TypeRole::CallArgument, 15),
        expected_type_call_close(1, 15),
    ];
    let (green, exit, remainder, records) =
        run_type_normalized_with_recoveries("T(", 13, LineEntry::InLine, None, None);
    assert_eq!(green.to_string(), "T(");
    assert!(matches!(
        exit,
        Some(NormalizedExit::Complete(
            Err(Either::Right(_)),
            LineEntry::InLine
        ))
    ));
    assert_eq!(remainder, "");
    assert_eq!(records, expected);
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .map(|node| {
                usize::from(node.text_range().start())..usize::from(node.text_range().end())
            })
            .collect::<Vec<_>>(),
        [2..2, 2..2],
    );
}

#[test]
fn type_call_t3b_argument_errors_keep_exact_native_children_and_continuation() {
    let cases = [
        ("T(@A)", 2..3, vec![(SyntaxKind::Unknown, "@")], vec!["A"]),
        (
            "T(@ A)",
            2..4,
            vec![(SyntaxKind::Unknown, "@"), (SyntaxKind::Whitespace, " ")],
            vec!["A"],
        ),
        (
            "T(@@A)",
            2..4,
            vec![(SyntaxKind::Unknown, "@"), (SyntaxKind::Unknown, "@")],
            vec!["A"],
        ),
        (
            "T(@/*c*/ A)",
            2..9,
            vec![
                (SyntaxKind::Unknown, "@"),
                (SyntaxKind::BlockComment, "/*c*/"),
                (SyntaxKind::Whitespace, " "),
            ],
            vec!["A"],
        ),
        (
            "T(@ @@A)",
            2..6,
            vec![
                (SyntaxKind::Unknown, "@"),
                (SyntaxKind::Whitespace, " "),
                (SyntaxKind::Unknown, "@"),
                (SyntaxKind::Unknown, "@"),
            ],
            vec!["A"],
        ),
        (
            "T(@ , A)",
            2..3,
            vec![(SyntaxKind::Unknown, "@")],
            vec!["A"],
        ),
        (
            "T(@\n  A)",
            2..3,
            vec![(SyntaxKind::Unknown, "@")],
            vec!["A"],
        ),
        (
            "T(@\r\n  A)",
            2..3,
            vec![(SyntaxKind::Unknown, "@")],
            vec!["A"],
        ),
        ("T(@\n  )", 2..3, vec![(SyntaxKind::Unknown, "@")], vec![]),
    ];

    for (source, error_range, expected_children, expected_arguments) in cases {
        let expected = expected_type_call_argument_error(0, error_range.clone());
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(records, [expected.clone()], "{source:?}");
        let root = SyntaxNode::new_root(green.clone());
        let call = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeCallTail)
            .expect("TypeCallTail");
        let error = call
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("CallArgument Error");
        assert_eq!(
            usize::from(error.text_range().start())..usize::from(error.text_range().end()),
            error_range,
            "{source:?}",
        );
        assert_eq!(
            error
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .map(|token| (token.kind(), token.text().to_owned()))
                .collect::<Vec<_>>(),
            expected_children
                .iter()
                .map(|(kind, text)| (*kind, (*text).to_owned()))
                .collect::<Vec<_>>(),
            "{source:?}",
        );
        assert_eq!(
            call.children()
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            expected_arguments,
            "{source:?}",
        );
        if source == "T(@ , A)" {
            let space = call
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| {
                    token.kind() == SyntaxKind::Whitespace
                        && usize::from(token.text_range().start()) == 3
                })
                .expect("Call-owned gap before separator");
            assert_eq!(
                usize::from(space.text_range().start())..usize::from(space.text_range().end()),
                3..4
            );
            let comma = call
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::Comma)
                .expect("Call-owned explicit separator");
            assert_eq!(
                usize::from(comma.text_range().start())..usize::from(comma.text_range().end()),
                4..5
            );
        }

        let frozen = frozen_recovery_ids(std::slice::from_ref(&expected));
        let (frozen_green, frozen_exit, frozen_records) =
            run_type_with_recoveries(source, Some(&frozen));
        assert_eq!(frozen_green, green, "{source:?}");
        assert!(
            matches!(frozen_exit, Some(Err(Either::Right(_)))),
            "{source:?}"
        );
        assert_eq!(frozen_records, frozen, "{source:?}");
    }
}

#[test]
fn type_call_t3b_argument_error_maps_global_records_without_shifting_local_cst() {
    let source = "T(@ A)";
    let (green, exit, remainder, records) =
        run_type_normalized_with_recoveries(source, 13, LineEntry::InLine, None, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    assert!(matches!(
        exit,
        Some(NormalizedExit::Complete(
            Err(Either::Right(_)),
            LineEntry::InLine
        ))
    ));
    assert_eq!(records, [expected_type_call_argument_error(0, 15..17)]);
    let error = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("CallArgument Error");
    assert_eq!(
        usize::from(error.text_range().start())..usize::from(error.text_range().end()),
        2..4,
    );
}

#[test]
fn type_call_t3b_frozen_error_mismatch_preserves_diagnostic_cursor_and_slot() {
    let mut mismatched = expected_type_call_argument_error(7, 2..4);
    mismatched.site.range = 2..3;
    Arc::make_mut(&mut mismatched.unexpected)[0] = UnexpectedSyntax::Token {
        range: 2..3,
        category: UnexpectedCategory::OtherCharacter,
    };
    Arc::make_mut(&mut mismatched.expectations)[0].range = 2..3;
    let operators = OperatorTable::empty();
    let mut input = "T(@ A)";
    let mut recover = Recover::new(&operators);
    let frozen = [mismatched];
    let mut output = GreenNodeBuilder::reconcile(&frozen);
    output.start_node(SyntaxKind::Root.into());
    let before_diagnostics = output.diagnostic_position();
    let before_slots = output.recovery_slot_count();
    assert_eq!(before_diagnostics, (Some(8), 0));
    assert_eq!(before_slots, 0);
    let mismatch = catch_unwind(AssertUnwindSafe(|| {
        let _ = super::super::type_expr::type_expr(In::new(&mut input, &mut recover, &mut output));
    }));
    assert!(mismatch.is_err());
    assert_eq!(output.diagnostic_position(), before_diagnostics);
    assert_eq!(output.recovery_slot_count(), before_slots);
    drop(output);
}

#[test]
fn type_call_t3b_close_errors_retry_matching_close_and_preserve_native_leading() {
    let cases = [
        (
            "T(])",
            vec![expected_type_call_close_error(0, 2..3)],
            Some(3..4),
        ),
        (
            "T(A]",
            vec![
                expected_type_call_close_error(0, 3..4),
                expected_type_call_close(1, 4),
            ],
            None,
        ),
        (
            "T(A] )",
            vec![expected_type_call_close_error(0, 3..4)],
            Some(5..6),
        ),
        (
            "T(A]/*c*/)",
            vec![expected_type_call_close_error(0, 3..4)],
            Some(9..10),
        ),
        (
            "T(A]] )",
            vec![
                expected_type_call_close_error(0, 3..4),
                expected_type_call_close_error(1, 4..5),
            ],
            Some(6..7),
        ),
        (
            "T(A] @)",
            vec![
                expected_type_call_close_error(0, 3..4),
                expected_type_call_close_error(1, 5..6),
            ],
            Some(6..7),
        ),
        (
            "T(A] @",
            vec![
                expected_type_call_close_error(0, 3..4),
                expected_type_call_close_error(1, 5..6),
                expected_type_call_close(2, 6),
            ],
            None,
        ),
    ];

    for (source, expected, close_range) in cases {
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(records, expected, "{source:?}");
        let root = SyntaxNode::new_root(green.clone());
        let call = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeCallTail)
            .expect("TypeCallTail");
        let errors = call
            .children()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(
            errors
                .iter()
                .map(|error| {
                    error
                        .children_with_tokens()
                        .filter_map(|element| element.into_token())
                        .map(|token| (token.kind(), token.text().to_owned()))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>(),
            expected
                .iter()
                .filter(|record| record.kind == RecoveryKind::Error)
                .map(|record| vec![(
                    SyntaxKind::Unknown,
                    source[record.site.range.clone()].to_owned()
                )])
                .collect::<Vec<_>>(),
            "{source:?}",
        );
        assert_eq!(
            call.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::RParen)
                .map(|token| {
                    usize::from(token.text_range().start())..usize::from(token.text_range().end())
                }),
            close_range,
            "{source:?}",
        );

        let frozen = frozen_recovery_ids(&expected);
        let (frozen_green, _, frozen_records) = run_type_with_recoveries(source, Some(&frozen));
        assert_eq!(frozen_green, green, "{source:?}");
        assert_eq!(frozen_records, frozen, "{source:?}");
    }
}

#[test]
fn type_call_t3b_close_recovery_suspends_contextual_but_preserves_caller_boundaries() {
    let operators = OperatorTable::empty();
    let active_close_stops = stops_for(TokenKind::RBracket)
        & !super::super::operator::STOP_COMMA
        & !super::super::operator::STOP_SEMICOLON;
    let source = "T(A} ] tail";
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let (exit, _) = super::super::type_expr::type_expr_with_caller_stops_for_test(
        In::new(&mut input, &mut recover, &mut output),
        active_close_stops,
        0,
        0,
    )
    .expect("accepted TypeCall");
    let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) = exit else {
        panic!("caller close remains pending after local Call mismatch")
    };
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), "T(A}");
    assert_eq!(
        records,
        [
            expected_type_call_close_error(0, 3..4),
            expected_type_call_close(1, 4),
        ]
    );
    assert_eq!(
        pending.payload_view().token_kind(),
        Some(TokenKind::RBracket)
    );
    assert_eq!(emit_pending_leading_text(&mut pending), " ");
    assert_eq!(input, " tail");

    let source = "T(A] @ with";
    let (green, exit, primary_found, _, _, records, _, _) =
        run_required_type_with_outer_boundary_and_recoveries(
            source,
            super::super::type_expr::TypeOuterBoundary::WITH,
            false,
            None,
        );
    assert!(primary_found);
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
    ));
    assert_eq!(green.to_string(), source);
    assert_eq!(
        records,
        [
            expected_type_call_close_error(0, 3..4),
            expected_type_call_close_error(1, 5..6),
            expected_type_call_close_error(2, 7..11),
            expected_type_call_close(3, 11),
        ]
    );

    let frozen = frozen_recovery_ids(&records);
    let (frozen_green, frozen_exit, _, _, _, frozen_records, _, _) =
        run_required_type_with_outer_boundary_and_recoveries(
            source,
            super::super::type_expr::TypeOuterBoundary::WITH,
            false,
            Some(&frozen),
        );
    assert!(matches!(
        frozen_exit,
        NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
    ));
    assert_eq!(frozen_green, green);
    assert_eq!(frozen_records, frozen);
}

#[test]
fn type_delimited_owner_recovers_missing_items_and_close_at_eof() {
    for (source, owner, missing) in [
        ("T(", SyntaxKind::TypeCallTail, 2),
        ("(A", SyntaxKind::ParenthesizedTypeGroup, 1),
        ("T(A,", SyntaxKind::TypeCallTail, 2),
        ("T(,A)", SyntaxKind::TypeCallTail, 1),
        ("T(A,,B)", SyntaxKind::TypeCallTail, 1),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("type delimited owner");
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T(A ");
    assert_eq!(green.to_string(), "T(A ");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("type call tail");
    assert_eq!(
        call.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::LParen, "(".to_owned()),
            (SyntaxKind::Identifier, "A".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
        ]
    );
}

#[test]
fn type_delimited_owner_retries_malformed_initial_items() {
    for (source, owner, recovered) in [
        ("T(@A)", SyntaxKind::TypeCallTail, "A"),
        ("(@A)", SyntaxKind::ParenthesizedTypeGroup, "A"),
        ("'[@A]", SyntaxKind::EffectRowType, "A"),
        ("T(@, A)", SyntaxKind::TypeCallTail, "A"),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("type delimited owner");
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            owner
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Identifier && token.text() == recovered),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T(@");
    assert_eq!(green.to_string(), "T(@");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("type call tail");
    assert_eq!(
        call.children()
            .filter(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
            .count(),
        2
    );
}

#[test]
fn named_record_type_keeps_field_and_separator_ownership() {
    let source = "{a: A, b: List(Int)}";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let record = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .expect("named record type");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        2
    );
    assert_eq!(
        record
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::LBrace, "{".to_owned()),
            (SyntaxKind::Comma, ",".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::RBrace, "}".to_owned()),
        ]
    );
}

#[test]
fn named_record_type_claims_a_same_line_complete_field_head_before_type_apply() {
    let (green, exit) = run_type("{a: F b: B}");
    assert_eq!(green.to_string(), "{a: F b: B}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let record = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .expect("named record type");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        2
    );
    assert_eq!(
        record
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        !record
            .descendants()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );
    assert_eq!(
        record
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Whitespace)
            .map(|token| token.text().to_owned())
            .collect::<Vec<_>>(),
        [" "]
    );

    let (green, exit) = run_type("{a: F B}");
    assert_eq!(green.to_string(), "{a: F B}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let record = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .expect("named record type");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        1
    );
    assert_eq!(
        record
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        0
    );
    assert_eq!(
        record
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeApplyArgument)
            .count(),
        1
    );
}

#[test]
fn named_record_type_recovers_leading_and_repeated_commas() {
    for (source, fields, missing) in [
        ("{,a: A}", 1, 1),
        ("{a: A,,b: B}", 2, 1),
        ("{,}", 0, 1),
        ("{a: A,}", 1, 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            fields,
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }
}

#[test]
fn named_record_type_recovers_a_missing_field_before_eof_or_outer_close() {
    let (green, exit) = run_type("{a: A,");
    assert_eq!(green.to_string(), "{a: A,");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );

    let (green, exit) = run_type("{a: A,]");
    assert_eq!(green.to_string(), "{a: A,");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::RBracket)
    ));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );
}

#[test]
fn named_record_type_recovers_a_missing_close() {
    for (source, missing) in [("{", 1), ("{a: A", 1), ("{a: A,", 2)] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(
            SyntaxNode::new_root(green)
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("{a: A]");
    assert_eq!(green.to_string(), "{a: A");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::RBracket)
    ));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn named_record_type_retries_a_malformed_whole_field() {
    for (source, fields, error_text) in [
        ("{@ a: A}", 1, "@"),
        ("{@, b: B}", 1, "@"),
        ("{..A, b: B}", 1, "..A"),
        ("{@}", 0, "@"),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let record = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            fields,
            "{source:?}"
        );
        let error = record
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("whole-field error");
        assert_eq!(error.text(), error_text, "{source:?}");
        assert!(
            !error
                .descendants()
                .any(|node| node.kind() == SyntaxKind::TypeRecordField),
            "{source:?}"
        );
    }
}

#[test]
fn named_record_whole_field_retry_keeps_qualified_newline_with_the_record() {
    let source = "{@\n  a: A}";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let record = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .expect("named record type");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        1
    );
    assert_eq!(
        record
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("whole-field error")
            .text(),
        "@"
    );
    assert_eq!(
        record
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Newline)
            .map(|token| token.text().to_owned())
            .collect::<Vec<_>>(),
        ["\n"]
    );
}

#[test]
fn named_record_field_retries_a_malformed_name_only_with_a_colon_skeleton() {
    for (source, error_text) in [
        ("{@: A}", "@"),
        ("{'a: A}", "'a"),
        ("{1: A}", "1"),
        ("{@ !: A}", "@ !"),
        ("{@ (): A}", "@ ()"),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            1,
            "{source:?}"
        );
        let field = record
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeRecordField)
            .expect("type record field");
        assert_eq!(
            field
                .children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            field
                .children()
                .find(|node| node.kind() == SyntaxKind::Error)
                .expect("name error")
                .text(),
            error_text,
            "{source:?}"
        );
        assert_eq!(
            field
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn named_record_type_recovers_an_invalid_semicolon_separator() {
    for (source, fields) in [
        ("{a: A;b: B}", 2),
        ("{a: A; b: B}", 2),
        ("{a: A;}", 1),
        ("{;b: B}", 1),
        ("{;}", 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            fields,
            "{source:?}"
        );
        let error = record
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("separator error");
        assert_eq!(error.text(), ";", "{source:?}");
    }

    let source = "{a: A; (\n) b: B}";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let record = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .expect("named record type");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        2
    );
    assert_eq!(
        record
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("separator error")
            .text(),
        "; (\n)"
    );
}

#[test]
fn named_record_field_recovers_missing_colon_and_type() {
    for (source, fields) in [
        ("{a}", 1),
        ("{a, b: B}", 2),
        ("{a A}", 1),
        ("{a:}", 1),
        ("{a:\nb: B}", 2),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            fields,
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("{a for 'x: T}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ForallType)
    );
}

#[test]
fn named_record_field_recovers_a_missing_name_before_colon() {
    for (source, fields, missing) in [
        ("{: A}", 1, 1),
        ("{a: A, : B}", 2, 1),
        ("{a: A\n: B}", 2, 1),
        ("{:}", 1, 2),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            fields,
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }
}

#[test]
fn named_record_field_retries_a_malformed_colon_slot() {
    for (source, error_text) in [("{a @ : B}", "@"), ("{a :: B}", "::"), ("{a @ B}", "@")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let field = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeRecordField)
            .expect("type record field");
        assert_eq!(
            field
                .children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        let error = field
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("colon error");
        assert_eq!(error.text(), error_text, "{source:?}");
        assert!(
            field
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Identifier && token.text() == "B"),
            "{source:?}"
        );
    }
}

#[test]
fn named_record_field_retries_a_malformed_type_slot() {
    for (source, fields) in [("{a: @ B}", 1), ("{a: @, b: B}", 2), ("{a: @\nb: B}", 2)] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            fields,
            "{source:?}"
        );
        let field = record
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeRecordField)
            .expect("first type record field");
        let error = field
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("type error");
        assert_eq!(error.text(), "@", "{source:?}");
        assert_eq!(
            field
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn named_record_type_accepts_layout_and_type_tails() {
    let layout = "{\n  a: A\n  b: B\n}";
    let (green, exit) = run_type(layout);
    assert_eq!(green.to_string(), layout);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let record = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .expect("named record type");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        2
    );

    let applied = run_type("F {a: A} -> Out").0;
    assert_eq!(applied.to_string(), "F {a: A} -> Out");
    let top = top_type_expression(&applied);
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeArrowTail)
    );

    let (adjacent, exit) = run_type("F{a:A}");
    assert_eq!(adjacent.to_string(), "F");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::LBrace)
    ));
    assert!(
        !SyntaxNode::new_root(adjacent)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::NamedRecordType)
    );
}

#[test]
fn forall_type_is_contextual_terminal_primary() {
    let source = "for 'a: A -> A";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let top = top_type_expression(&green);
    assert_eq!(
        top.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::ForallType]
    );
    let forall = top
        .children()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type");
    assert_eq!(
        forall
            .children()
            .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
            .count(),
        1
    );
    assert!(
        forall
            .descendants()
            .any(|node| node.kind() == SyntaxKind::TypeArrowTail)
    );

    let layout = "for\n  'a\n  'b:\n    Pair('a, 'b)";
    let (green, exit) = run_type(layout);
    assert_eq!(green.to_string(), layout);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
            .count(),
        2
    );

    for source in ["(for 'a: T)", "F(for 'a: T)", "A -> for 'a: T"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(
            SyntaxNode::new_root(green)
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::ForallType)
                .count(),
            1,
            "{source:?}"
        );
    }

    let grouped = run_type("(for 'a: T)::Result").0;
    let top = top_type_expression(&grouped);
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::ParenthesizedTypeGroup)
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );
}

#[test]
fn forall_type_recovers_clean_mandatory_slots_without_cascading() {
    for source in ["for", "for 'a", "for 'a:", "for'a: T", "for 'a T", "for: T"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("for\n");
    assert_eq!(green.to_string(), "for\n");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let forall = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type");
    assert!(
        !forall
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Newline)
    );
    assert!(
        root.children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Newline && token.text() == "\n")
    );
}

#[test]
fn forall_type_recovers_root_separators_as_its_own_malformed_phase() {
    for (source, separator, binders) in [
        ("for, 'a: T", ",", 2),
        ("for; 'a: T", ";", 2),
        ("for 'a, 'b: T", ",", 3),
        ("for 'a; 'b: T", ";", 3),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        let errors = forall
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(
            errors
                .iter()
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            [separator],
            "{source:?}"
        );
        assert_eq!(
            errors[0].parent().map(|node| node.kind()),
            Some(SyntaxKind::ForallTypeBinder),
            "{source:?}"
        );
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            0,
            "{source:?}"
        );
        assert_eq!(
            forall
                .children()
                .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
                .count(),
            binders,
            "{source:?}"
        );
    }
}

#[test]
fn forall_type_separator_recovery_keeps_first_binder_and_continuation_phases_distinct() {
    for (source, consumed, separator) in [("for, T", "for,", ","), ("for; T", "for;", ";")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), consumed, "{source:?}");
        assert!(matches!(
            exit,
            Some(Err(Either::Left(item)))
                if item.payload_view().token_kind() == Some(TokenKind::Identifier)
                    && item.payload_view().spelling() == Some("T")
                    && item.leading_view().has_ordinary_trivia()
                    && !item.leading_view().has_ordinary_newline()
        ));
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        let error = forall
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("separator error");
        assert_eq!(error.text().to_string(), separator, "{source:?}");
        assert_eq!(
            error.parent().map(|node| node.kind()),
            Some(SyntaxKind::ForallTypeBinder),
            "{source:?}"
        );
        assert!(
            !forall
                .descendants()
                .any(|node| node.kind() == SyntaxKind::TypeExpression),
            "{source:?}"
        );
        assert!(
            !forall
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    for (source, separator) in [("for 'a, T", ","), ("for 'a; T", ";")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        let error = forall
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("separator error");
        assert_eq!(error.text().to_string(), separator, "{source:?}");
        assert_eq!(
            error.parent().map(|node| node.kind()),
            Some(SyntaxKind::ForallTypeBinder),
            "{source:?}"
        );
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            forall
                .descendants()
                .any(|node| node.kind() == SyntaxKind::TypeExpression),
            "{source:?}"
        );
    }
}

#[test]
fn forall_type_handoffs_active_owner_separators_without_absorbing_trivia() {
    for source in ["F(for, A)", "F(for; A)", "F(for 'a, B)", "F(for 'a; B)"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let forall = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        assert!(
            !forall
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{source:?}"
        );
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !forall
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| { matches!(token.kind(), SyntaxKind::Comma | SyntaxKind::Semicolon) }),
            "{source:?}"
        );
        let call = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeCallTail)
            .expect("type call");
        assert_eq!(
            call.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| matches!(token.kind(), SyntaxKind::Comma | SyntaxKind::Semicolon))
                .count(),
            1,
            "{source:?}"
        );
    }

    let source = "F(for 'a /* gap */, B)";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let forall = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type");
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("type call");
    assert!(!forall.text().to_string().contains("/* gap */"));
    assert!(call.text().to_string().contains("/* gap */"));
}

#[test]
fn forall_type_body_separators_follow_the_active_owner() {
    for (source, separator) in [("for 'a: , T", ","), ("for 'a: ; T", ";")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            [separator],
            "{source:?}"
        );
        assert!(
            !forall
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    for source in ["F(for 'a: , T)", "F(for 'a: ; T)"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let forall = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        assert!(
            !forall
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{source:?}"
        );
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn forall_type_handoffs_record_and_variant_payload_separators() {
    for (source, separator, record_error) in [
        ("{a: for 'a, b: B}", ",", None),
        ("{a: for 'a; b: B}", ";", Some(";")),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let forall = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        assert!(
            !forall
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{source:?}"
        );
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !forall
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| { matches!(token.kind(), SyntaxKind::Comma | SyntaxKind::Semicolon) }),
            "{source:?}"
        );
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            2,
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            record_error.into_iter().collect::<Vec<_>>(),
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| matches!(token.kind(), SyntaxKind::Comma | SyntaxKind::Semicolon))
                .map(|token| token.text().to_string())
                .collect::<Vec<_>>(),
            [separator],
            "{source:?}"
        );
    }

    let (green, exit) = run_type(":{A for 'a, B}");
    assert_eq!(green.to_string(), ":{A for 'a, B}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let forall = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type");
    assert!(
        !forall
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );
    assert_eq!(
        forall
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .count(),
        2
    );
}

#[test]
fn forall_type_recovers_malformed_phase_runs_and_retries() {
    for (source, expected_error, expected_missing, expected_binders) in [
        ("for @", "@", 0, 1),
        ("for T", "T", 0, 1),
        ("for @ 'a: T", "@", 0, 2),
        ("for @: T", "@", 0, 1),
        ("for 'a @", "@", 0, 1),
        ("for 'a @ 'b: T", "@", 0, 3),
        ("for 'a @: T", "@", 0, 1),
        ("for 'a @ T", "@", 0, 1),
        ("for 'a: @", "@", 0, 1),
        ("for 'a: @ T", "@", 0, 1),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            [expected_error],
            "{source:?}"
        );
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected_missing,
            "{source:?}"
        );
        assert_eq!(
            forall
                .children()
                .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
                .count(),
            expected_binders,
            "{source:?}"
        );
    }

    let first_binder = run_type("for @ 'a: T").0;
    let first_binder = SyntaxNode::new_root(first_binder)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForallTypeBinder)
        .expect("recovered first binder");
    assert!(
        first_binder
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );

    let malformed_colon = run_type("for 'a @: T").0;
    let malformed_colon = SyntaxNode::new_root(malformed_colon)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type");
    assert!(
        malformed_colon
            .children()
            .any(|node| node.kind() == SyntaxKind::Error)
    );

    let (green, exit) = run_type("for 'a @\nT");
    assert_eq!(green.to_string(), "for 'a @");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::Identifier)
                && item.payload_view().spelling() == Some("T")
                && item.leading_view().has_ordinary_newline()
    ));
    let root = SyntaxNode::new_root(green);
    let forall = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type");
    assert!(
        !forall
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Newline)
    );

    let deeper = run_type("for\n  'a @\n  'b: T").0;
    let deeper = SyntaxNode::new_root(deeper);
    assert_eq!(
        deeper
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
            .count(),
        3
    );

    let nested = run_type("for (@: T) 'a: T").0;
    let nested = SyntaxNode::new_root(nested);
    assert_eq!(
        nested
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["(@: T)"]
    );

    let nested_newline = run_type("for (@\n) 'a: T").0;
    let nested_newline = SyntaxNode::new_root(nested_newline);
    assert_eq!(
        nested_newline
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["(@\n)"]
    );
    assert_eq!(
        nested_newline
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
            .count(),
        2
    );

    for source in ["for 'a @ (@: T)", "for 'a @ ('b)"] {
        let (green, _) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        assert!(
            !forall
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Colon),
            "{source:?}"
        );
    }
}

#[test]
fn forall_type_does_not_reclassify_type_apply_for() {
    for source in ["forx 'a", "forall 'a", "for_ 'a"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::ForallType),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("F for 'a: T");
    assert_eq!(green.to_string(), "F for 'a");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::Colon)
    ));
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ForallType)
    );
}

#[test]
fn effect_row_type_keeps_its_compound_opener_and_items() {
    for (source, item_kind) in [
        ("'[]", None),
        ("'[e]", Some(SyntaxKind::Identifier)),
        ("'['e]", Some(SyntaxKind::SigilIdentifier)),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let row = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::EffectRowType)
            .expect("effect row type");
        assert_eq!(
            row.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::Apostrophe | SyntaxKind::LBracket | SyntaxKind::RBracket
                    )
                })
                .map(|token| (token.kind(), token.text().to_owned()))
                .collect::<Vec<_>>(),
            [
                (SyntaxKind::Apostrophe, "'".to_owned()),
                (SyntaxKind::LBracket, "[".to_owned()),
                (SyntaxKind::RBracket, "]".to_owned()),
            ],
            "{source:?}"
        );
        assert_eq!(
            row.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::Identifier | SyntaxKind::SigilIdentifier
                    )
                })
                .map(|token| token.kind())
                .collect::<Vec<_>>(),
            item_kind.into_iter().collect::<Vec<_>>(),
            "{source:?}"
        );
    }
}

#[test]
fn effect_row_type_composes_with_layout_and_tails() {
    let layout = "'[\n  A, B;\n  C\n  D\n]";
    let (green, exit) = run_type(layout);
    assert_eq!(green.to_string(), layout);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let row = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::EffectRowType)
        .expect("effect row type");
    assert_eq!(
        row.children()
            .filter(|node| node.kind() == SyntaxKind::TypeExpression)
            .count(),
        4
    );

    let (green, exit) = run_type("Foo '['e] -> Out");
    assert_eq!(green.to_string(), "Foo '['e] -> Out");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let top = top_type_expression(&green);
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeArrowTail)
    );

    let path = run_type("'[e]::Result").0;
    assert!(
        top_type_expression(&path)
            .children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );

    for source in ["'", "' [e]", "'/*c*/[e]"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), "", "{source:?}");
        assert!(exit.is_none(), "{source:?}");
    }
}

#[test]
fn polymorphic_variant_type_keeps_two_level_boundaries() {
    for (source, tags, payloads) in [
        (":{}", 0, 0),
        (":{A Int, B}", 2, 1),
        (":{A Int Bool}", 1, 2),
        (":{A Int\nB}", 2, 1),
        (":{A,}", 1, 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let variant = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(
            variant
                .children()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
                .count(),
            tags,
            "{source:?}"
        );
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
                .count(),
            payloads,
            "{source:?}"
        );
    }

    let nested = ":{\n  A Pair(\n    Int,\n    Bool\n  )\n  B\n}";
    let (green, exit) = run_type(nested);
    assert_eq!(green.to_string(), nested);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(
        variant
            .children()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .count(),
        2
    );

    let (green, exit) = run_type(":{A [e] T X}");
    assert_eq!(green.to_string(), ":{A [e] T X}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
            .count(),
        2
    );
}

#[test]
fn polymorphic_variant_type_recovers_outer_tag_positions() {
    for (source, tags, missing) in [
        (":{,A}", 1, 1),
        (":{,,A}", 1, 2),
        (":{A,,B}", 2, 1),
        (":{,}", 0, 1),
        (":{A,}", 1, 0),
        (":{A,,}", 1, 1),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(
            variant
                .children()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
                .count(),
            tags,
            "{source:?}"
        );
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }
}

#[test]
fn shared_delimited_pv_carriers_preserve_extent_and_outer_continuation() {
    // Selected successor contracts: recovery-authority amendment §4 and its
    // retained P/E extent tables. Numeric Calls are one TagName recovery, not
    // the legacy numeric-head/separate-payload split.
    for (owner, owner_start, rows) in [
        (
            SyntaxKind::ParenthesizedTypeGroup,
            2,
            [
                (":{( }", 4, Some(3), 2),
                (":{(A, }", 6, Some(5), 2),
                (":{(A; }", 6, Some(5), 2),
                (":{(A }", 5, Some(4), 1),
                (":{(A}", 4, None, 1),
                (":{(A )}", 6, Some(4), 0),
            ],
        ),
        (
            SyntaxKind::EffectRowType,
            2,
            [
                (":{'[ }", 5, Some(4), 2),
                (":{'[F, }", 7, Some(6), 2),
                (":{'[F; }", 7, Some(6), 2),
                (":{'[F }", 6, Some(5), 1),
                (":{'[F}", 5, None, 1),
                (":{'[F ]}", 7, Some(5), 0),
            ],
        ),
        (
            SyntaxKind::TypeCallTail,
            5,
            [
                (":{123( }", 7, Some(6), 2),
                (":{123(F, }", 9, Some(8), 2),
                (":{123(F; }", 9, Some(8), 2),
                (":{123(F }", 8, Some(7), 1),
                (":{123(F}", 7, None, 1),
                (":{123(F )}", 9, Some(7), 0),
            ],
        ),
    ] {
        for (base, end, gap_start, missing_count) in rows {
            for origin in [0, 23] {
                let at = origin + end;
                let mut expected = vec![expected_type_error(
                    0,
                    TypeRole::PolymorphicVariantTagName,
                    origin + 2..at,
                )];
                if missing_count == 2 {
                    expected.push(expected_type_expression_missing(
                        1,
                        match owner {
                            SyntaxKind::TypeCallTail => TypeRole::CallArgument,
                            SyntaxKind::ParenthesizedTypeGroup => TypeRole::ParenthesizedItem,
                            SyntaxKind::EffectRowType => TypeRole::EffectRowItem,
                            _ => unreachable!(),
                        },
                        at,
                    ));
                }
                if missing_count > 0 {
                    match owner {
                        SyntaxKind::TypeCallTail => {
                            expected.push(expected_type_call_close(expected.len() as u32, at))
                        }
                        SyntaxKind::ParenthesizedTypeGroup => {
                            expected.push(expected_parenthesized_close(expected.len() as u32, at));
                        }
                        SyntaxKind::EffectRowType => {
                            expected.push(pe_recovery::close(
                                expected.len() as u32,
                                true,
                                at..at,
                                None,
                            ));
                        }
                        _ => unreachable!(),
                    }
                }
                for suffix in ["", "::Next"] {
                    let source = format!("{base}{suffix}");
                    let root = assert_complete_type_recovery(&source, origin, &expected);
                    let errors = root
                        .descendants()
                        .filter(|node| node.kind() == SyntaxKind::Error)
                        .collect::<Vec<_>>();
                    assert_eq!(errors.len(), 1, "{source:?}");
                    let error = &errors[0];
                    assert_eq!(error.text().to_string(), &base[2..end]);
                    assert_eq!(usize::from(error.text_range().start()), 8 + 2);
                    assert_eq!(usize::from(error.text_range().end()), 8 + end);
                    let delimited = error
                        .descendants()
                        .find(|node| node.kind() == owner)
                        .expect("delimited owner inside TagName Error");
                    assert_eq!(delimited.text().to_string(), &base[owner_start..end]);
                    assert_eq!(usize::from(delimited.text_range().start()), 8 + owner_start);
                    let gaps = delimited
                        .children_with_tokens()
                        .filter(|child| child.kind() == SyntaxKind::Whitespace)
                        .collect::<Vec<_>>();
                    assert_eq!(gaps.len(), usize::from(gap_start.is_some()));
                    if let Some(start) = gap_start {
                        assert_eq!(gaps[0].to_string(), " ");
                        assert_eq!(usize::from(gaps[0].text_range().start()), 8 + start);
                        assert_eq!(usize::from(gaps[0].text_range().end()), 8 + start + 1);
                    }
                    let missing = delimited
                        .children()
                        .filter(|node| node.kind() == SyntaxKind::Missing)
                        .collect::<Vec<_>>();
                    assert_eq!(missing.len(), missing_count, "{source:?}");
                    for node in missing {
                        assert!(node.text_range().is_empty());
                        assert_eq!(usize::from(node.text_range().start()), 8 + end);
                    }
                    if base[..end].ends_with([')', ']']) {
                        let close = if owner == SyntaxKind::EffectRowType {
                            SyntaxKind::RBracket
                        } else {
                            SyntaxKind::RParen
                        };
                        assert!(delimited.children_with_tokens().any(|child| {
                            child.kind() == close
                                && usize::from(child.text_range().start()) == 8 + end - 1
                                && usize::from(child.text_range().end()) == 8 + end
                        }));
                    }
                    let top = root
                        .children()
                        .find(|node| node.kind() == SyntaxKind::TypeExpression)
                        .expect("outer Type expression");
                    let variant = top
                        .children()
                        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
                        .expect("outer PV");
                    let close = variant
                        .children_with_tokens()
                        .find(|child| child.kind() == SyntaxKind::RBrace)
                        .expect("native outer PV close");
                    assert_eq!(usize::from(close.text_range().start()), 8 + end);
                    assert_eq!(usize::from(close.text_range().end()), 8 + end + 1);
                    assert!(
                        !error
                            .descendants_with_tokens()
                            .any(|child| { child.kind() == SyntaxKind::RBrace })
                    );
                    let tails = top
                        .children()
                        .filter(|node| node.kind() == SyntaxKind::TypePathTail)
                        .collect::<Vec<_>>();
                    assert_eq!(tails.len(), usize::from(!suffix.is_empty()));
                    if !suffix.is_empty() {
                        assert_eq!(tails[0].text().to_string(), suffix);
                        assert_eq!(usize::from(tails[0].text_range().start()), 8 + base.len());
                    }
                }
            }
        }
    }
}

#[test]
fn shared_delimited_pv_prefix_and_recursive_reservations_keep_owned_ranges() {
    for (base, expected) in [
        (
            ":{@ (A }",
            vec![
                expected_type_error(0, TypeRole::PolymorphicVariantTag, 2..3),
                expected_type_error(1, TypeRole::PolymorphicVariantTagName, 4..7),
                expected_parenthesized_close(2, 7),
            ],
        ),
        (
            ":{@ '[F }",
            vec![
                expected_type_error(0, TypeRole::PolymorphicVariantTag, 2..3),
                expected_type_error(1, TypeRole::PolymorphicVariantTagName, 4..8),
                pe_recovery::close(2, true, 8..8, None),
            ],
        ),
        (
            ":{:{(A }}",
            vec![
                expected_type_error(0, TypeRole::PolymorphicVariantTagName, 2..8),
                expected_type_error(1, TypeRole::PolymorphicVariantTagName, 4..7),
                expected_parenthesized_close(2, 7),
            ],
        ),
        (
            ":{:{'[F }}",
            vec![
                expected_type_error(0, TypeRole::PolymorphicVariantTagName, 2..9),
                expected_type_error(1, TypeRole::PolymorphicVariantTagName, 4..8),
                pe_recovery::close(2, true, 8..8, None),
            ],
        ),
    ] {
        for suffix in ["", "::Next"] {
            let source = format!("{base}{suffix}");
            let root = assert_complete_type_recovery(&source, 0, &expected);
            let errors = root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .collect::<Vec<_>>();
            let error_records = expected
                .iter()
                .filter(|record| record.kind == RecoveryKind::Error)
                .collect::<Vec<_>>();
            assert_eq!(errors.len(), error_records.len());
            for (node, record) in errors.iter().zip(error_records) {
                assert_eq!(
                    usize::from(node.text_range().start()),
                    8 + record.site.range.start
                );
                assert_eq!(
                    usize::from(node.text_range().end()),
                    8 + record.site.range.end
                );
                assert_eq!(node.text().to_string(), &base[record.site.range.clone()]);
            }
            assert_eq!(
                errors[0].descendants().any(|node| node == errors[1]),
                base.starts_with(":{:{")
            );
            for variant in root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            {
                assert!(variant.children_with_tokens().any(|child| {
                    child.kind() == SyntaxKind::RBrace
                        && child.text_range().end() == variant.text_range().end()
                }));
            }
            let top = root
                .children()
                .find(|node| node.kind() == SyntaxKind::TypeExpression)
                .expect("outer Type expression");
            assert_eq!(
                top.children()
                    .filter(|node| node.kind() == SyntaxKind::TypePathTail)
                    .count(),
                usize::from(!suffix.is_empty())
            );
        }
    }
}

#[test]
fn shared_delimited_recovery_preserves_accepted_numeric_and_pv_types() {
    // Numeric Type atoms and tight Calls are accepted by the standalone Type
    // grammar. The PV controls have valid names and whitespace-separated payloads.
    for (source, owner) in [
        ("123", None),
        ("123(F)", Some(SyntaxKind::TypeCallTail)),
        ("(F)", Some(SyntaxKind::ParenthesizedTypeGroup)),
        ("'[F]", Some(SyntaxKind::EffectRowType)),
        (":{A}", Some(SyntaxKind::PolymorphicVariantType)),
        (":{A (F)}", Some(SyntaxKind::ParenthesizedTypeGroup)),
        (":{A '[F]}", Some(SyntaxKind::EffectRowType)),
    ] {
        let root = assert_complete_type_recovery(source, 0, &[]);
        assert!(
            !root
                .descendants()
                .any(|node| { matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing) }),
            "{source:?}"
        );
        if let Some(owner) = owner {
            assert!(root.descendants().any(|node| node.kind() == owner));
        }
        if source.starts_with("123") {
            let top = root
                .children()
                .find(|node| node.kind() == SyntaxKind::TypeExpression)
                .expect("accepted numeric Type");
            assert!(top.children_with_tokens().any(|child| {
                child.kind() == SyntaxKind::Integer && child.to_string() == "123"
            }));
            assert_eq!(
                top.children()
                    .filter(|node| node.kind() == SyntaxKind::TypeCallTail)
                    .count(),
                usize::from(owner.is_some())
            );
        }
    }
}

#[test]
fn polymorphic_variant_structured_tag_name_orders_fresh_and_frozen_recovery() {
    let source = ":{@ (A}";
    let (green, exit, records) = run_type_with_recoveries(source, None);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        records,
        [
            expected_type_error(0, TypeRole::PolymorphicVariantTag, 2..3),
            expected_type_error(1, TypeRole::PolymorphicVariantTagName, 4..6),
            expected_parenthesized_close(2, 6),
        ]
    );

    let root = SyntaxNode::new_root(green.clone());
    let tag = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
        .expect("recovered polymorphic-variant tag");
    let tag_children = tag.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(tag_children[0].kind(), SyntaxKind::Error);
    assert_eq!(tag_children[0].to_string(), "@");
    assert_eq!(tag_children[1].kind(), SyntaxKind::Whitespace);
    assert_eq!(tag_children[1].to_string(), " ");
    assert_eq!(tag_children[2].kind(), SyntaxKind::Error);
    let structured = tag_children[2]
        .clone()
        .into_node()
        .expect("structured tag-name Error");
    let group = structured
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedTypeGroup)
        .expect("nested parenthesized Type group");
    assert_eq!(group.text().to_string(), "(A");
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    let variant = tag
        .ancestors()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic-variant owner");
    assert!(
        variant
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::RBrace && token.text() == "}")
    );

    let (frozen_green, frozen_exit, frozen_records) =
        run_type_with_recoveries(source, Some(&records));
    assert_eq!(frozen_green, green);
    assert!(matches!(frozen_exit, Some(Err(Either::Right(_)))));
    assert_eq!(frozen_records, records);
}

#[test]
fn polymorphic_variant_recursive_structured_tag_names_are_lifo_and_reusable() {
    let source = ":{:{123}}";
    let (green, exit, records) = run_type_with_recoveries(source, None);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        records,
        [
            expected_type_error(0, TypeRole::PolymorphicVariantTagName, 2..8),
            expected_type_error(1, TypeRole::PolymorphicVariantTagName, 4..7),
        ]
    );
    let root = SyntaxNode::new_root(green.clone());
    let structured = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Error)
        .collect::<Vec<_>>();
    assert_eq!(
        structured
            .iter()
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        [":{123}", "123"]
    );
    assert!(structured[0].descendants().any(|node| {
        node.kind() == SyntaxKind::PolymorphicVariantType && node.text().to_string() == ":{123}"
    }));

    let (frozen_green, frozen_exit, frozen_records) =
        run_type_with_recoveries(source, Some(&records));
    assert_eq!(frozen_green, green);
    assert!(matches!(frozen_exit, Some(Err(Either::Right(_)))));
    assert_eq!(frozen_records, records);
}

#[test]
fn polymorphic_variant_structured_tag_name_single_and_valid_controls() {
    let (green, exit, records) = run_type_with_recoveries(":{123}", None);
    assert_eq!(green.to_string(), ":{123}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        records,
        [expected_type_error(
            0,
            TypeRole::PolymorphicVariantTagName,
            2..5,
        )]
    );

    let (green, exit, records) = run_type_with_recoveries(":{A}", None);
    assert_eq!(green.to_string(), ":{A}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(records.is_empty());
}

#[test]
fn polymorphic_variant_structured_frozen_mismatches_reject_each_position() {
    let source = ":{@ (A}";
    let (_, _, records) = run_type_with_recoveries(source, None);
    for (index, mismatch_source, item_origin, outer_closes) in [
        (0, source, 0, 0),
        (1, ":{(A}", 2, 0),
        (
            2,
            "(A}",
            4,
            super::super::type_expr::with_type_outer_close(0, TokenKind::RBrace),
        ),
    ] {
        let mut mismatched = records.clone();
        Arc::make_mut(&mut mismatched[index].expectations)[0].expected =
            ExpectedSyntax::TypeExpression;
        let operators = OperatorTable::empty();
        let mut input = mismatch_source;
        let mut recover = Recover::new(&operators);
        let mut output = GreenNodeBuilder::reconcile(&mismatched);
        output.start_node(SyntaxKind::Root.into());
        for record in records.iter().take(index) {
            commit_record_draft(&mut output, record);
        }
        let before_diagnostics = output.diagnostic_position();
        let before_slots = output.recovery_slot_count();
        assert_eq!(before_diagnostics, (Some(3), index));
        assert_eq!(before_slots, index);
        let mismatch = catch_unwind(AssertUnwindSafe(|| {
            let _ = super::super::type_expr::type_expr_with_caller_stops_for_test(
                In::new(&mut input, &mut recover, &mut output),
                0,
                outer_closes,
                item_origin,
            )
            .expect("focused mismatch source is a Type candidate");
        }));
        assert!(mismatch.is_err(), "frozen recovery position {index}");
        assert_eq!(output.diagnostic_position(), before_diagnostics);
        assert_eq!(output.recovery_slot_count(), before_slots);
        // The panic invalidates this partially emitted builder. Only the
        // pre-mismatch cursor/slot surface is inspected; it is then discarded.
        drop(output);
    }
}

#[test]
fn parenthesized_close_initial() {
    assert_outer_parenthesized_close(":{(}", None);
    assert_local_parenthesized_close("(]", None);
}

#[test]
fn parenthesized_close_post_head() {
    assert_outer_parenthesized_close(":{(A}", None);
    assert_local_parenthesized_close("(A]", None);
}

#[test]
fn parenthesized_close_malformed_retry() {
    assert_outer_parenthesized_close(":{(@}", Some(3..4));
    assert_local_parenthesized_close("(@]", Some(1..2));
}

#[test]
fn parenthesized_close_after_separator() {
    assert_outer_parenthesized_close(":{(A,}", None);
    assert_local_parenthesized_close("(A,]", None);
}

#[test]
fn parenthesized_close_matching() {
    let (green, exit, records) = run_type_with_recoveries("(A)", None);
    assert_eq!(green.to_string(), "(A)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(records.is_empty());
}

#[test]
fn parenthesized_close_eof() {
    let (green, exit, records) = run_type_with_recoveries("(A", None);
    assert_eq!(green.to_string(), "(A");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(records, [expected_parenthesized_close(0, 2)]);
}

#[test]
fn parenthesized_close_trivia_prefixed_outer_anchor() {
    let source = ":{(A }";
    let (green, exit, records) = run_type_with_recoveries(source, None);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        records,
        [
            expected_type_error(0, TypeRole::PolymorphicVariantTagName, 2..5),
            expected_parenthesized_close(1, 5),
        ]
    );
    assert_eq!(parenthesized_group(&green).text().to_string(), "(A ");
}

#[test]
fn parenthesized_close_abstract_boundary() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let source = "> > (A\n> > ```\nouter";
    let (green, exit, remainder, records) = run_type_normalized_with_recoveries(
        source,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
        None,
    );
    assert_eq!(green.to_string(), "> > (A");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("parenthesized group must preserve the abstract fence boundary")
    };
    assert!(boundary.payload_view().is_boundary());
    assert!(boundary.leading_view().has_ordinary_newline());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(records, [expected_parenthesized_close(0, 6)]);
}

#[test]
fn parenthesized_close_nonclose_caller_boundary() {
    let operators = OperatorTable::empty();
    let mut input = "(A with";
    let mut recover = Recover::new(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let (exit, successor_origin) = super::super::type_expr::type_expr_with_caller_stops_for_test(
        In::new(&mut input, &mut recover, &mut output),
        super::super::operator::STOP_WITH,
        0,
        0,
    )
    .expect("accepted parenthesized Type");
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), "(A ");
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
        panic!("active non-close caller boundary must remain pending")
    };
    assert_eq!(item.payload_view().spelling(), Some("with"));
    assert_eq!(item.leading_view().remaining_physical_parts(), 0);
    assert_eq!(input, "");
    assert_eq!(successor_origin, 7);
    assert_eq!(records, [expected_parenthesized_close(0, 3)]);
}

#[test]
fn parenthesized_close_active_caller_close_is_typed_and_preserves_successor() {
    let operators = OperatorTable::empty();
    let active_close_stops = stops_for(TokenKind::RBracket)
        & !super::super::operator::STOP_COMMA
        & !super::super::operator::STOP_SEMICOLON;
    for (source, emitted, missing_count, expected) in [
        (
            "( ] tail",
            "( ",
            2,
            vec![
                pe_recovery::item(0, false, 2..2, false),
                expected_parenthesized_close(1, 2),
            ],
        ),
        (
            "(A ] tail",
            "(A ",
            1,
            vec![expected_parenthesized_close(0, 3)],
        ),
        (
            "(@ ] tail",
            "(@",
            1,
            vec![
                pe_recovery::item(0, false, 1..2, true),
                expected_parenthesized_close(1, 2),
            ],
        ),
        (
            "(A, ] tail",
            "(A, ",
            2,
            vec![
                pe_recovery::item(0, false, 4..4, false),
                expected_parenthesized_close(1, 4),
            ],
        ),
    ] {
        let mut input = source;
        let mut recover = Recover::new(&operators);
        assert_eq!(recover.mark(), ());
        assert!(std::ptr::eq(recover.operators(), &operators));
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (exit, successor_origin) =
            super::super::type_expr::type_expr_with_caller_stops_for_test(
                In::new(&mut input, &mut recover, &mut output),
                active_close_stops,
                0,
                0,
            )
            .expect("accepted parenthesized Type");
        let diagnostics = output.diagnostic_position();
        let slots = output.recovery_slot_count();
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        let NormalizedExit::Complete(Err(Either::Left(item)), line_entry) = exit else {
            panic!("active caller-owned close must remain pending: {source:?}")
        };
        let before_gap = emitted.trim_end();
        let control_source = source
            .strip_prefix(before_gap)
            .expect("emitted prefix belongs to source");
        let (
            mut control_item,
            control_origin,
            control_line,
            control_remainder,
            mark,
            same_operators,
        ) = scan_type_item_control(control_source, before_gap.len(), &operators);
        let gap_emitted = emitted.ends_with(' ');
        if gap_emitted {
            assert_eq!(emit_pending_leading_text(&mut control_item), " ");
        }
        assert_eq!(green.to_string(), emitted, "{source:?}");
        assert_eq!(
            parenthesized_group(&green)
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing_count,
            "{source:?}"
        );
        assert_eq!(records, expected, "{source:?}");
        assert_eq!(slots, expected.len(), "{source:?}");
        assert_eq!(diagnostics, (Some(expected.len() as u32), 0), "{source:?}");
        assert_eq!(item, control_item, "{source:?}");
        assert_eq!(
            item.payload_view().token_kind(),
            Some(TokenKind::RBracket),
            "{source:?}"
        );
        assert_eq!(
            item.leading_view().remaining_physical_parts(),
            usize::from(!gap_emitted)
        );
        assert_eq!(item.leading_view().has_ordinary_trivia(), !gap_emitted);
        assert!(!item.leading_view().has_ordinary_newline());
        assert_eq!(input, control_remainder, "{source:?}");
        assert_eq!(successor_origin, control_origin, "{source:?}");
        assert_eq!(line_entry, control_line, "{source:?}");
        assert_eq!(mark, ());
        assert!(same_operators);
    }
}

#[test]
fn shared_delimited_horizontal_boundary_phases_are_fresh_frozen_exact() {
    let origin = 23;
    for (owner, opener, outer_close) in [
        (SyntaxKind::TypeCallTail, "T(", TokenKind::RBracket),
        (SyntaxKind::ParenthesizedTypeGroup, "(", TokenKind::RBracket),
        (SyntaxKind::EffectRowType, "'[", TokenKind::RParen),
    ] {
        for (slot, fresh_slot) in [("", true), ("F", false), ("F,", true), ("F;", true)] {
            for gap in [" ", " \t "] {
                for (payload, caller_stops, outer_closes) in [
                    ("}", stops_for(TokenKind::RBrace), 0),
                    (":", super::super::operator::STOP_COLON, 0),
                    (
                        if outer_close == TokenKind::RBracket {
                            "]"
                        } else {
                            ")"
                        },
                        0,
                        super::super::type_expr::with_type_outer_close(0, outer_close),
                    ),
                ] {
                    let caller_stops = caller_stops
                        & !super::super::operator::STOP_COMMA
                        & !super::super::operator::STOP_SEMICOLON;
                    let prefix = format!("{opener}{slot}");
                    let emitted = format!("{prefix}{gap}");
                    let source = format!("{emitted}{payload} tail");
                    let at = origin + emitted.len();
                    let expected = match owner {
                        SyntaxKind::TypeCallTail if fresh_slot => vec![
                            expected_type_expression_missing(0, TypeRole::CallArgument, at),
                            expected_type_call_close(1, at),
                        ],
                        SyntaxKind::TypeCallTail => vec![expected_type_call_close(0, at)],
                        SyntaxKind::ParenthesizedTypeGroup if fresh_slot => vec![
                            pe_recovery::item(0, false, at..at, false),
                            expected_parenthesized_close(1, at),
                        ],
                        SyntaxKind::ParenthesizedTypeGroup => {
                            vec![expected_parenthesized_close(0, at)]
                        }
                        SyntaxKind::EffectRowType if fresh_slot => vec![
                            pe_recovery::item(0, true, at..at, false),
                            pe_recovery::close(1, true, at..at, None),
                        ],
                        SyntaxKind::EffectRowType => {
                            vec![pe_recovery::close(0, true, at..at, None)]
                        }
                        _ => unreachable!(),
                    };
                    for (context_label, context) in t4p_seeded_contexts() {
                        let fresh = run_contextual_type_snapshot(
                            &source,
                            context,
                            caller_stops,
                            outer_closes,
                            origin,
                            LineEntry::InLine,
                            None,
                            None,
                        );
                        assert_eq!(
                            fresh.green.to_string(),
                            format!("sentinel{emitted}"),
                            "{source:?}, {context_label}"
                        );
                        assert_eq!(fresh.records, expected, "{source:?}, {context_label}");
                        assert_eq!(fresh.slots, expected.len());
                        assert_eq!(fresh.diagnostics, (Some(expected.len() as u32), 0));
                        assert_eq!(fresh.mark, ());
                        assert!(fresh.same_operators);
                        let NormalizedExit::Complete(Err(Either::Left(mut pending)), line) =
                            fresh.exit
                        else {
                            panic!("raw boundary: {source:?}")
                        };
                        let (mut control, control_origin, control_line, remainder, _, _) =
                            scan_type_item_control(
                                &source[prefix.len()..],
                                origin + prefix.len(),
                                &OperatorTable::empty(),
                            );
                        assert_eq!(emit_pending_leading_text(&mut control), gap);
                        assert_eq!(pending, control, "{source:?}");
                        assert_eq!(pending.payload_view().spelling(), Some(payload));
                        assert_eq!(emit_pending_leading_text(&mut pending), "");
                        assert_eq!(fresh.successor_origin, control_origin);
                        assert_eq!(line, control_line);
                        assert_eq!(fresh.remainder, remainder);
                        assert_eq!(remainder, " tail");
                        let node = SyntaxNode::new_root(fresh.green.clone())
                            .descendants()
                            .find(|node| node.kind() == owner)
                            .expect("immediate owner");
                        let children = node
                            .children_with_tokens()
                            .filter(|child| {
                                child.kind() == SyntaxKind::Whitespace
                                    || child.kind() == SyntaxKind::Missing
                            })
                            .collect::<Vec<_>>();
                        assert_eq!(children.len(), if fresh_slot { 3 } else { 2 }, "{source:?}");
                        assert_eq!(children[0].kind(), SyntaxKind::Whitespace);
                        assert_eq!(children[0].to_string(), gap);
                        assert_eq!(
                            usize::from(children[0].text_range().start()),
                            8 + prefix.len()
                        );
                        assert_eq!(
                            usize::from(children[0].text_range().end()),
                            8 + emitted.len()
                        );
                        for missing in &children[1..] {
                            assert_eq!(missing.kind(), SyntaxKind::Missing);
                            assert_eq!(
                                usize::from(missing.text_range().start()),
                                8 + emitted.len()
                            );
                            assert!(missing.text_range().is_empty());
                        }
                        assert!(
                            !node
                                .descendants()
                                .any(|node| node.kind() == SyntaxKind::Error)
                        );
                        let frozen = frozen_recovery_ids(&expected);
                        let replay = run_contextual_type_snapshot(
                            &source,
                            context,
                            caller_stops,
                            outer_closes,
                            origin,
                            LineEntry::InLine,
                            None,
                            Some(&frozen),
                        );
                        assert_eq!(replay.green, fresh.green);
                        assert_eq!(replay.records, frozen);
                        assert_eq!(replay.slots, frozen.len());
                        assert_eq!(replay.diagnostics.1, frozen.len());
                        assert_eq!(replay.successor_origin, control_origin);
                        assert_eq!(replay.remainder, remainder);
                        assert_eq!(replay.mark, ());
                        assert!(replay.same_operators);
                        let NormalizedExit::Complete(Err(Either::Left(replayed)), replay_line) =
                            replay.exit
                        else {
                            panic!("frozen raw boundary: {source:?}")
                        };
                        assert_eq!(replayed, control);
                        assert_eq!(replay_line, line);
                    }
                }
            }
        }
    }
}

#[test]
fn shared_delimited_horizontal_local_closes_and_fresh_else_keep_owner_admission() {
    for (owner, opener, close) in [
        (SyntaxKind::TypeCallTail, "T(", ")"),
        (SyntaxKind::ParenthesizedTypeGroup, "(", ")"),
        (SyntaxKind::EffectRowType, "'[", "]"),
    ] {
        for slot in ["", "F", "F,", "F;"] {
            let source = format!("{opener}{slot} \t{close}");
            let (green, _, records) = run_type_with_recoveries(&source, None);
            assert_eq!(green.to_string(), source);
            assert!(records.is_empty());
            let node = SyntaxNode::new_root(green.clone())
                .descendants()
                .find(|node| node.kind() == owner)
                .expect("immediate owner");
            let children = node.children_with_tokens().collect::<Vec<_>>();
            assert_eq!(children[children.len() - 2].kind(), SyntaxKind::Whitespace);
            assert_eq!(children[children.len() - 2].to_string(), " \t");
            assert_eq!(children.last().unwrap().to_string(), close);
            assert!(
                !node
                    .descendants()
                    .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
            );
            let (replayed, _, frozen_records) = run_type_with_recoveries(&source, Some(&[]));
            assert_eq!(replayed, green);
            assert!(frozen_records.is_empty());
        }
        for slot in ["", "F,", "F;"] {
            let source = format!("{opener}{slot} else{close}");
            let context = super::super::type_expr::TypeMlContext::INACTIVE;
            let run = run_contextual_type_snapshot(
                &source,
                context,
                super::super::operator::STOP_ELSE,
                0,
                0,
                LineEntry::InLine,
                None,
                None,
            );
            let frozen = frozen_recovery_ids(&run.records);
            let replay = run_contextual_type_snapshot(
                &source,
                context,
                super::super::operator::STOP_ELSE,
                0,
                0,
                LineEntry::InLine,
                None,
                Some(&frozen),
            );
            assert_eq!(replay.green, run.green);
            assert_eq!(replay.records, frozen);
            assert_eq!(replay.slots, run.slots);
            assert_eq!(replay.diagnostics.1, frozen.len());
            assert_eq!(replay.successor_origin, run.successor_origin);
            assert_eq!(replay.remainder, run.remainder);
            match (&run.exit, &replay.exit) {
                (
                    NormalizedExit::Complete(Err(Either::Left(item)), line),
                    NormalizedExit::Complete(Err(Either::Left(replayed)), replay_line),
                ) => {
                    assert_eq!(replayed, item);
                    assert_eq!(replay_line, line);
                }
                (
                    NormalizedExit::Complete(Err(Either::Right(end)), line),
                    NormalizedExit::Complete(Err(Either::Right(replayed)), replay_line),
                ) => {
                    assert_eq!(replayed.item, end.item);
                    assert_eq!(replay_line, line);
                }
                _ => panic!("fresh/frozen caller-stop exit: {source:?}"),
            }
            if owner == SyntaxKind::TypeCallTail {
                let prefix = format!("{opener}{slot} ");
                assert_eq!(run.green.to_string(), format!("sentinel{prefix}"));
                assert_eq!(
                    run.records,
                    [
                        expected_type_expression_missing(0, TypeRole::CallArgument, prefix.len()),
                        expected_type_call_close(1, prefix.len()),
                    ]
                );
                let NormalizedExit::Complete(Err(Either::Left(pending)), LineEntry::InLine) =
                    run.exit
                else {
                    panic!("Call retains explicit ELSE stop")
                };
                assert_eq!(pending.payload_view().spelling(), Some("else"));
                assert!(pending.leading_view().is_grammar_empty());
                assert_eq!(run.remainder, close);
            } else {
                assert_eq!(run.green.to_string(), format!("sentinel{source}"));
                assert!(run.records.is_empty());
                assert_eq!(run.slots, 0);
                assert_eq!(run.diagnostics, (Some(0), 0));
                assert!(
                    SyntaxNode::new_root(run.green)
                        .descendants_with_tokens()
                        .any(|element| element.kind() == SyntaxKind::Identifier
                            && element.to_string() == "else")
                );
                assert_eq!(run.remainder, "");
            }
        }
    }
}

#[test]
fn shared_delimited_horizontal_correction_preserves_nonhorizontal_handoff() {
    let caller_stops = stops_for(TokenKind::RBrace)
        & !super::super::operator::STOP_COMMA
        & !super::super::operator::STOP_SEMICOLON;
    for (prefix, owner) in [
        ("T(F", SyntaxKind::TypeCallTail),
        ("(F", SyntaxKind::ParenthesizedTypeGroup),
        ("'[F", SyntaxKind::EffectRowType),
    ] {
        for leading in [" /* gap */ ", "\n ", "\r\n ", " // gap\n "] {
            let source = format!("{prefix}{leading}}} tail");
            let run = run_contextual_type_snapshot(
                &source,
                super::super::type_expr::TypeMlContext::INACTIVE,
                caller_stops,
                0,
                0,
                LineEntry::InLine,
                None,
                None,
            );
            assert_eq!(
                run.green.to_string(),
                format!("sentinel{prefix}"),
                "{source:?}"
            );
            let NormalizedExit::Complete(Err(Either::Left(mut pending)), line) = run.exit else {
                panic!("nonhorizontal boundary remains pending: {source:?}")
            };
            let (control, control_origin, control_line, remainder, _, _) = scan_type_item_control(
                &source[prefix.len()..],
                prefix.len(),
                &OperatorTable::empty(),
            );
            assert_eq!(pending, control);
            assert_eq!(emit_pending_leading_text(&mut pending), leading);
            assert_eq!(run.successor_origin, control_origin);
            assert_eq!(line, control_line);
            assert_eq!(run.remainder, remainder);
            let at = prefix.len();
            let expected = match owner {
                SyntaxKind::TypeCallTail => vec![expected_type_call_close(0, at)],
                SyntaxKind::ParenthesizedTypeGroup => vec![expected_parenthesized_close(0, at)],
                SyntaxKind::EffectRowType => vec![pe_recovery::close(0, true, at..at, None)],
                _ => unreachable!(),
            };
            assert_eq!(run.records, expected);
            let frozen = frozen_recovery_ids(&expected);
            let replay = run_contextual_type_snapshot(
                &source,
                super::super::type_expr::TypeMlContext::INACTIVE,
                caller_stops,
                0,
                0,
                LineEntry::InLine,
                None,
                Some(&frozen),
            );
            assert_eq!(replay.green, run.green);
            assert_eq!(replay.records, frozen);
            let NormalizedExit::Complete(Err(Either::Left(replayed)), replay_line) = replay.exit
            else {
                panic!("frozen nonhorizontal boundary: {source:?}")
            };
            assert_eq!(replayed, control);
            assert_eq!(replay_line, line);
        }
    }
}

#[test]
fn shared_delimited_horizontal_fresh_outer_closes_continue_in_their_actual_owner() {
    for (owner, source, at, close_kind) in [
        (
            SyntaxKind::ParenthesizedTypeGroup,
            "G T[( ]->U",
            6,
            SyntaxKind::RBracket,
        ),
        (
            SyntaxKind::ParenthesizedTypeGroup,
            "G T[(F, ]->U",
            8,
            SyntaxKind::RBracket,
        ),
        (
            SyntaxKind::ParenthesizedTypeGroup,
            "G T[(F; ]->U",
            8,
            SyntaxKind::RBracket,
        ),
        (
            SyntaxKind::TypeCallTail,
            "G T[T( ]->U",
            7,
            SyntaxKind::RBracket,
        ),
        (
            SyntaxKind::TypeCallTail,
            "G T[T(F, ]->U",
            9,
            SyntaxKind::RBracket,
        ),
        (
            SyntaxKind::TypeCallTail,
            "G T[T(F; ]->U",
            9,
            SyntaxKind::RBracket,
        ),
        (SyntaxKind::EffectRowType, "G ('[ )", 6, SyntaxKind::RParen),
        (
            SyntaxKind::EffectRowType,
            "G ('[F, )",
            8,
            SyntaxKind::RParen,
        ),
        (
            SyntaxKind::EffectRowType,
            "G ('[F; )",
            8,
            SyntaxKind::RParen,
        ),
    ] {
        let (green, exit, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let expected = match owner {
            SyntaxKind::TypeCallTail => vec![
                expected_type_expression_missing(0, TypeRole::CallArgument, at),
                expected_type_call_close(1, at),
            ],
            SyntaxKind::ParenthesizedTypeGroup => vec![
                pe_recovery::item(0, false, at..at, false),
                expected_parenthesized_close(1, at),
            ],
            SyntaxKind::EffectRowType => vec![
                pe_recovery::item(0, true, at..at, false),
                pe_recovery::close(1, true, at..at, None),
            ],
            _ => unreachable!(),
        };
        assert_eq!(records, expected, "{source:?}");
        let root = SyntaxNode::new_root(green.clone());
        let inner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .unwrap();
        let children = inner
            .children_with_tokens()
            .filter(|child| matches!(child.kind(), SyntaxKind::Whitespace | SyntaxKind::Missing))
            .collect::<Vec<_>>();
        assert_eq!(children.len(), 3, "{source:?}");
        assert_eq!(children[0].kind(), SyntaxKind::Whitespace);
        assert_eq!(children[0].to_string(), " ");
        assert_eq!(usize::from(children[0].text_range().end()), at);
        for child in &children[1..] {
            assert_eq!(child.kind(), SyntaxKind::Missing);
            assert_eq!(usize::from(child.text_range().start()), at);
            assert!(child.text_range().is_empty());
        }
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error)
        );
        let outer_close = root
            .descendants_with_tokens()
            .find(|element| element.kind() == close_kind)
            .unwrap();
        assert_eq!(usize::from(outer_close.text_range().start()), at);
        assert!(
            !inner
                .descendants_with_tokens()
                .any(|element| element == outer_close)
        );
        if close_kind == SyntaxKind::RBracket {
            assert!(
                root.descendants_with_tokens()
                    .any(|element| element.kind() == SyntaxKind::Arrow)
            );
            assert!(
                root.descendants_with_tokens()
                    .any(|element| element.kind() == SyntaxKind::Identifier
                        && element.to_string() == "U")
            );
        }
        let frozen = frozen_recovery_ids(&expected);
        let (replayed, replay_exit, frozen_records) =
            run_type_with_recoveries(source, Some(&frozen));
        assert_eq!(replayed, green);
        assert_eq!(frozen_records, frozen);
        assert!(matches!(replay_exit, Some(Err(Either::Right(_)))));
    }
}

#[test]
fn type_delimited_owner_routing_types_effect_but_keeps_bracket_close_recovery_raw() {
    for (source, expected) in [
        ("'[A", vec![pe_recovery::close(0, true, 3..3, None)]),
        ("[e", vec![]),
    ] {
        let (green, _, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(records, expected, "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }
}

#[test]
fn polymorphic_variant_nt8_same_slot_trivia_has_one_exact_prefix_record() {
    let source = ":{@ A}";
    let (green, exit, records) = run_type_with_recoveries(source, None);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        records,
        [expected_type_error(
            0,
            TypeRole::PolymorphicVariantTag,
            2..3,
        )]
    );
    let tag = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
        .expect("same-slot recovered tag");
    let children = tag.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children[0].kind(), SyntaxKind::Error);
    assert_eq!(children[0].to_string(), "@");
    assert_eq!(children[1].kind(), SyntaxKind::Whitespace);
    assert_eq!(children[1].to_string(), " ");
    assert_eq!(children[2].kind(), SyntaxKind::Identifier);
    assert_eq!(children[2].to_string(), "A");

    let source = ":{@ . A}";
    let (green, exit, records) = run_type_with_recoveries(source, None);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        records,
        [expected_type_error(
            0,
            TypeRole::PolymorphicVariantTag,
            2..5,
        )]
    );
    let tag = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
        .expect("multi-Item same-slot recovered tag");
    let children = tag.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children[0].kind(), SyntaxKind::Error);
    assert_eq!(children[0].to_string(), "@ .");
    assert_eq!(children[1].kind(), SyntaxKind::Whitespace);
    assert_eq!(children[1].to_string(), " ");
    assert_eq!(children[2].kind(), SyntaxKind::Identifier);
    assert_eq!(children[2].to_string(), "A");
}

#[test]
fn rb_pv_rejected_candidate_preservation() {
    let operators = OperatorTable::empty();
    let frozen = [];

    let mut candidate_input = ":x";
    let mut candidate_recover = Recover::new(&operators);
    let candidate_mark = candidate_recover.mark();
    let candidate_operators = std::ptr::eq(candidate_recover.operators(), &operators);
    let mut candidate_output = GreenNodeBuilder::reconcile(&frozen);
    candidate_output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut candidate_output);
    let before_slots = candidate_output.recovery_slot_count();
    let before_diagnostics = candidate_output.diagnostic_position();
    let exit = super::super::type_expr::type_expr(In::new(
        &mut candidate_input,
        &mut candidate_recover,
        &mut candidate_output,
    ));
    assert!(exit.is_none());
    let candidate_slots = candidate_output.recovery_slot_count();
    let candidate_diagnostics = candidate_output.diagnostic_position();
    candidate_output.finish_node();
    let (candidate_green, candidate_records) = candidate_output.finish_with_recoveries();

    let control_input = ":x";
    let control_recover = Recover::new(&operators);
    let control_mark = control_recover.mark();
    let control_operators = std::ptr::eq(control_recover.operators(), &operators);
    let mut control_output = GreenNodeBuilder::reconcile(&frozen);
    control_output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut control_output);
    let control_slots = control_output.recovery_slot_count();
    let control_diagnostics = control_output.diagnostic_position();
    control_output.finish_node();
    let (control_green, control_records) = control_output.finish_with_recoveries();

    let candidate_pending: Option<Item> = None;
    let control_pending: Option<Item> = None;
    let candidate_successor_origin = 0;
    let control_successor_origin = 0;
    let candidate_line_entry = LineEntry::InLine;
    let control_line_entry = LineEntry::InLine;
    assert_eq!(candidate_green, control_green);
    assert_eq!(candidate_records, control_records);
    assert_eq!(candidate_slots, control_slots);
    assert_eq!(candidate_diagnostics, control_diagnostics);
    assert_eq!(candidate_input, control_input);
    assert_eq!(candidate_pending, control_pending);
    assert_eq!(candidate_successor_origin, control_successor_origin);
    assert_eq!(candidate_line_entry, control_line_entry);
    assert_eq!(candidate_mark, control_mark);
    assert_eq!(candidate_mark, ());
    assert!(candidate_operators && control_operators);
    assert_eq!(candidate_slots, before_slots);
    assert_eq!(candidate_diagnostics, before_diagnostics);
    assert_eq!(candidate_diagnostics, (Some(0), 0));
    assert_eq!(candidate_input, ":x");
    assert!(candidate_records.is_empty());
}

#[test]
fn rb_t_parenthesized_close_preserves_pending_state_and_sequence() {
    let operators = OperatorTable::empty();
    let frozen = [expected_parenthesized_close(0, 3)];

    let mut candidate_input: &'static str = "(A with";
    let mut candidate_recover = Recover::new(&operators);
    let candidate_mark = candidate_recover.mark();
    let candidate_operators = std::ptr::eq(candidate_recover.operators(), &operators);
    let mut candidate_output = GreenNodeBuilder::reconcile(&frozen);
    candidate_output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut candidate_output);
    let (candidate_exit, candidate_origin) =
        super::super::type_expr::type_expr_with_caller_stops_for_test(
            In::new(
                &mut candidate_input,
                &mut candidate_recover,
                &mut candidate_output,
            ),
            super::super::operator::STOP_WITH,
            0,
            0,
        )
        .expect("accepted parenthesized Type");
    let NormalizedExit::Complete(Err(Either::Left(candidate_item)), candidate_line) =
        candidate_exit
    else {
        panic!("active caller boundary must remain pending")
    };
    let candidate_diagnostics = candidate_output.diagnostic_position();
    let candidate_slots = candidate_output.recovery_slot_count();
    candidate_output.finish_node();
    let (candidate_green, candidate_records) = candidate_output.finish_with_recoveries();

    let (
        mut control_item,
        control_origin,
        control_line,
        control_input,
        control_mark,
        control_operators,
    ) = scan_type_item_control(" with", 2, &operators);
    let mut control_output = GreenNodeBuilder::reconcile(&frozen);
    control_output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut control_output);
    control_output.start_node(SyntaxKind::TypeExpression.into());
    control_output.start_node(SyntaxKind::ParenthesizedTypeGroup.into());
    control_output.token(SyntaxKind::LParen.into(), "(");
    control_output.start_node(SyntaxKind::TypeExpression.into());
    control_output.token(SyntaxKind::Identifier.into(), "A");
    control_output.finish_node();
    control_item.emit_all_remaining_leading(&mut control_output);
    control_output.start_node(SyntaxKind::Missing.into());
    control_output.finish_node();
    commit_record_draft(&mut control_output, &frozen[0]);
    control_output.finish_node();
    control_output.finish_node();
    let control_diagnostics = control_output.diagnostic_position();
    let control_slots = control_output.recovery_slot_count();
    control_output.finish_node();
    let (control_green, control_records) = control_output.finish_with_recoveries();

    assert_eq!(candidate_green, control_green);
    assert_eq!(candidate_records, control_records);
    assert_eq!(candidate_slots, control_slots);
    assert_eq!(candidate_diagnostics, control_diagnostics);
    assert_eq!(candidate_input, control_input);
    assert_eq!(candidate_item, control_item);
    assert_eq!(candidate_origin, control_origin);
    assert_eq!(candidate_line, control_line);
    assert_eq!(candidate_mark, control_mark);
    assert_eq!(candidate_mark, ());
    assert!(candidate_operators && control_operators);
    assert_eq!(candidate_records, frozen);
    assert_eq!(candidate_item.payload_view().spelling(), Some("with"));
    assert_eq!(candidate_item.leading_view().remaining_physical_parts(), 0);
    assert!(!candidate_item.leading_view().has_ordinary_trivia());
    assert!(!candidate_item.leading_view().has_ordinary_newline());
    assert_eq!(candidate_line, LineEntry::InLine);
    assert_eq!(candidate_input, "");
    assert_eq!(candidate_origin, 7);
    assert_eq!(candidate_diagnostics, (Some(1), 1));
    assert_eq!(candidate_slots, 1);
}

#[test]
fn polymorphic_variant_type_recovers_non_identifier_tag_primaries() {
    for (source, tag_text, payloads) in [
        (":{123}", "123", 0),
        (":{123 Int}", "123", 1),
        (":{for 'a: T}", "for 'a: T", 0),
        (":{:{A} B}", ":{A}", 1),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        let tags = variant
            .children()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .collect::<Vec<_>>();
        assert_eq!(tags.len(), 1, "{source:?}");
        let tag = &tags[0];
        let errors = tag
            .children()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{source:?}");
        let error = &errors[0];
        assert_eq!(error.text().to_string(), tag_text, "{source:?}");
        assert_eq!(
            error
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !tag.descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
        assert_eq!(
            tag.descendants()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
                .count(),
            payloads,
            "{source:?}"
        );
    }

    for source in [":{123, A}", ":{123\nA}"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(
            variant
                .children()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
                .count(),
            2,
            "{source:?}"
        );
        assert!(
            !variant
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    let (green, exit) = run_type(":{123]}");
    assert_eq!(green.to_string(), ":{123]}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["123", "]"]
    );
}

#[test]
fn polymorphic_variant_type_recovers_malformed_tag_runs() {
    fn polymorphic_variant_node(green: GreenNode) -> SyntaxNode {
        SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type")
    }

    for (source, tags, missing) in [
        (":{@}", 1, 0),
        (":{@", 1, 1),
        (":{@A}", 1, 0),
        (":{A@,B}", 3, 0),
        (":{@\nA}", 2, 0),
        (":{@]}", 1, 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = polymorphic_variant_node(green);
        assert_eq!(
            variant
                .children()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
                .count(),
            tags,
            "{source:?}"
        );
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .next()
                .expect("malformed tag error")
                .text()
                .to_string(),
            "@",
            "{source:?}"
        );
    }

    let (green, exit) = run_type(":{@123 Int}");
    assert_eq!(green.to_string(), ":{@123 Int}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    let tags = variant
        .children()
        .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
        .collect::<Vec<_>>();
    assert_eq!(tags.len(), 1);
    let errors = tags[0]
        .children()
        .filter(|node| node.kind() == SyntaxKind::Error)
        .collect::<Vec<_>>();
    assert_eq!(
        errors
            .iter()
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["@", "123"]
    );
    assert!(
        errors[0]
            .children()
            .all(|node| node.kind() != SyntaxKind::TypeExpression)
    );
    assert_eq!(
        errors[1]
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeExpression)
            .count(),
        1
    );
    assert_eq!(
        tags[0]
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
            .count(),
        1
    );
    assert!(
        !tags[0]
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    let (green, exit) = run_type(":{@ A}");
    assert_eq!(green.to_string(), ":{@ A}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    let tag = variant
        .children()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
        .expect("recovered tag");
    let error = tag
        .children()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("malformed tag error");
    assert_eq!(error.text().to_string(), "@");
    assert!(
        tag.children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );

    let (green, exit) = run_type(":{@ ,B}");
    assert_eq!(green.to_string(), ":{@ ,B}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    assert!(
        variant
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["@"]
    );

    let (green, exit) = run_type(":{@\n B}");
    assert_eq!(green.to_string(), ":{@\n B");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::RBrace)
    ));
    let top = top_type_expression(&green);
    let variant = top
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(variant.text().to_string(), ":{@");
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["@"]
    );
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );

    let (green, exit) = run_type(":{@;A}");
    assert_eq!(green.to_string(), ":{@;A}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["@", ";"]
    );

    let (green, exit) = run_type("F(:{@; B)");
    assert_eq!(green.to_string(), "F(:{@; B)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let variant = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(variant.text().to_string(), ":{@");
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["@"]
    );
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("outer call");
    assert!(
        call.children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Semicolon)
    );

    let (green, exit) = run_type("(:{@ )");
    assert_eq!(green.to_string(), "(:{@ )");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let variant = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(variant.text().to_string(), ":{@");
    let group = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedTypeGroup)
        .expect("outer group");
    assert!(
        group
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );
}

#[test]
fn polymorphic_variant_type_recovers_payload_boundaries_and_malformed_runs() {
    fn polymorphic_variant_node(green: GreenNode) -> SyntaxNode {
        SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type")
    }

    fn only_payload(variant: &SyntaxNode) -> SyntaxNode {
        let tag = variant
            .children()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .expect("polymorphic variant tag");
        tag.children()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
            .expect("polymorphic variant payload")
    }

    let (green, exit) = run_type(":{A(Int)}");
    assert_eq!(green.to_string(), ":{A(Int)}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    let payload = only_payload(&variant);
    assert_eq!(
        payload
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Missing, SyntaxKind::TypeExpression]
    );

    for (source, error_text) in [
        (":{A @Int}", "@"),
        (":{A @ Int}", "@"),
        (":{A @@Int}", "@@"),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = polymorphic_variant_node(green);
        let payload = only_payload(&variant);
        let error = payload
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("malformed payload error");
        assert_eq!(error.text().to_string(), error_text, "{source:?}");
        assert_eq!(
            error.parent().map(|node| node.kind()),
            Some(SyntaxKind::PolymorphicVariantPayload),
            "{source:?}"
        );
        assert_eq!(
            payload
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !variant
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    let (green, exit) = run_type(":{A @ Int}");
    assert_eq!(green.to_string(), ":{A @ Int}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let payload = only_payload(&polymorphic_variant_node(green));
    assert!(
        payload
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );

    for source in [":{A @}", ":{A @,B}", ":{A @;B}", ":{A @]}"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = polymorphic_variant_node(green);
        let payload = only_payload(&variant);
        assert_eq!(
            payload
                .children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            ["@"],
            "{source:?}"
        );
        assert!(
            !payload
                .children()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    let (green, exit) = run_type(":{A @,B}");
    assert_eq!(green.to_string(), ":{A @,B}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    assert_eq!(
        variant
            .children()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .count(),
        2
    );
    assert!(
        variant
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Comma)
    );

    for (source, separator) in [(":{A @ }", None), (":{A @ ;B}", Some(";"))] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = polymorphic_variant_node(green);
        let payload = only_payload(&variant);
        assert_eq!(payload.text().to_string(), " @", "{source:?}");
        assert_eq!(
            variant
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Whitespace)
                .map(|token| token.text().to_string())
                .collect::<Vec<_>>(),
            [" "],
            "{source:?}"
        );
        if let Some(separator) = separator {
            let error = variant
                .children()
                .find(|node| node.kind() == SyntaxKind::Error && node.text() == separator)
                .expect("local separator error");
            assert_eq!(
                error.parent().map(|node| node.kind()),
                Some(SyntaxKind::PolymorphicVariantType),
                "{source:?}"
            );
        } else {
            assert!(
                variant
                    .children_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(|token| token.kind() == SyntaxKind::RBrace)
            );
        }
    }

    let (green, exit) = run_type(":{A @\nB}");
    assert_eq!(green.to_string(), ":{A @\nB}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    assert_eq!(
        variant
            .children()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .count(),
        2
    );

    let (green, exit) = run_type(":{A @\n B}");
    assert_eq!(green.to_string(), ":{A @\n B");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::RBrace)
    ));
    let top = top_type_expression(&green);
    let variant = top
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(variant.text().to_string(), ":{A @");
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );

    for (source, boundary) in [(":{A @;B}", ";"), (":{A @]}", "]")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = polymorphic_variant_node(green);
        let error = variant
            .children()
            .find(|node| node.kind() == SyntaxKind::Error && node.text() == boundary)
            .expect("local payload boundary error");
        assert_eq!(
            error.parent().map(|node| node.kind()),
            Some(SyntaxKind::PolymorphicVariantType),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("F(:{A @ )");
    assert_eq!(green.to_string(), "F(:{A @ )");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let variant = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(variant.text().to_string(), ":{A @");
    let payload = only_payload(&variant);
    assert_eq!(
        payload
            .children()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["@"]
    );
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("outer call");
    assert!(
        call.children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );
    assert!(
        call.children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::RParen)
    );
}

#[test]
fn polymorphic_variant_type_recovers_local_separators_and_closes() {
    for source in [":{;A}", ":{A;B}", ":{A ; B}"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        let error = variant
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("local semicolon error");
        assert_eq!(error.text().to_string(), ";", "{source:?}");
        assert_eq!(
            error.parent().map(|node| node.kind()),
            Some(SyntaxKind::PolymorphicVariantType)
        );
    }

    for (source, missing) in [(":{]}", 0), (":{]", 1)] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        let error = variant
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("local close error");
        assert_eq!(error.text().to_string(), "]", "{source:?}");
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }
}

#[test]
fn polymorphic_variant_type_handoffs_outer_closes_and_separators() {
    let (green, exit) = run_type("(:{A)");
    assert_eq!(green.to_string(), "(:{A)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let variant = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        !variant
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );

    for source in ["F(:{A])", "F({a: :{A)"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let variant = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        let errors = variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>();
        assert_eq!(
            errors,
            if source == "F(:{A])" {
                vec!["]"]
            } else {
                vec![]
            }
        );
        if source == "F({a: :{A)" {
            let record = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::NamedRecordType)
                .expect("named record type");
            assert_eq!(
                record
                    .children()
                    .filter(|node| node.kind() == SyntaxKind::Missing)
                    .count(),
                1
            );
            let call = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::TypeCallTail)
                .expect("type call tail");
            assert!(
                !call
                    .children()
                    .any(|node| node.kind() == SyntaxKind::Missing)
            );
        }
    }

    for (source, outer) in [
        ("F(:{A; B)", SyntaxKind::TypeCallTail),
        ("{a: :{A; b: B}", SyntaxKind::NamedRecordType),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let variant = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(variant.text().to_string(), ":{A", "{source:?}");
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !variant
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error)
        );
        let owner = root
            .descendants()
            .find(|node| node.kind() == outer)
            .expect("outer owner");
        assert!(owner.text().to_string().contains(';'), "{source:?}");
    }

    for (source, outer) in [
        ("F(:{A;B)", SyntaxKind::TypeCallTail),
        ("{a: :{A;b:B}", SyntaxKind::NamedRecordType),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let variant = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(variant.text().to_string(), ":{A", "{source:?}");
        assert!(
            !variant
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Semicolon),
            "{source:?}"
        );
        let owner = root
            .descendants()
            .find(|node| node.kind() == outer)
            .expect("outer owner");
        assert!(
            owner
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Semicolon),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("F(:{A ])");
    assert_eq!(green.to_string(), "F(:{A ])");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let variant = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    let error = variant
        .children()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("local close error");
    assert_eq!(error.text().to_string(), "]");
    assert!(
        variant
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );

    let (green, exit) = run_type("F(:{A )");
    assert_eq!(green.to_string(), "F(:{A )");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let variant = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(variant.text().to_string(), ":{A");
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("type call tail");
    assert!(
        call.children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );
}

#[test]
fn polymorphic_variant_type_recovers_newline_and_eof_boundaries() {
    for (source, tags, missing) in [
        (":{A\nB}", 2, 0),
        (":{A\n}", 1, 0),
        (":{A\n", 1, 2),
        (":{", 0, 1),
        (":{A", 1, 1),
        (":{A,", 1, 2),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(
            variant
                .children()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
                .count(),
            tags,
            "{source:?}"
        );
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    let (green, exit) = run_type(":{A\n  B}");
    assert_eq!(green.to_string(), ":{A\n  B");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::RBrace)
    ));
    let top = top_type_expression(&green);
    let variant = top
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(variant.text().to_string(), ":{A");
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );
}

#[test]
fn polymorphic_variant_type_composes_with_type_tails() {
    let (green, exit) = run_type("F :{A} -> Out");
    assert_eq!(green.to_string(), "F :{A} -> Out");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let top = top_type_expression(&green);
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeArrowTail)
    );

    let path = run_type(":{A}::Result").0;
    assert!(
        top_type_expression(&path)
            .children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );

    let (green, exit) = run_type("F:{A}");
    assert_eq!(green.to_string(), "F");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    for source in [": {A}", ":/*comment*/{A}", ":\n{A}", ":"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), "", "{source:?}");
        assert!(exit.is_none(), "{source:?}");
    }
}

#[test]
fn bracket_rows_attach_at_leading_and_arrow_positions() {
    for (source, items) in [("[] T", 0), ("[e] T", 1), ("[e, f; g\nh] T", 4)] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let top = top_type_expression(&green);
        let row = top
            .children()
            .find(|node| node.kind() == SyntaxKind::BracketRow)
            .expect("leading bracket row");
        assert_eq!(
            row.children()
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .count(),
            items,
            "{source:?}"
        );
    }

    let source = "T [e, f] -> U -> V";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let top = top_type_expression(&green);
    let tail = top
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
        .expect("bracket row arrow tail");
    assert!(
        tail.children()
            .any(|node| node.kind() == SyntaxKind::BracketRow)
    );
    assert_eq!(
        top.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeArrowTail)
            .count(),
        2
    );

    for source in ["T -> [e] U", "F([e] T)", "[[e] T] U", "[e] F [io] -> U"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
    }
}

#[test]
fn bracket_row_arrow_is_mandatory_at_normal_boundaries() {
    for source in ["T [e]", "T [e] U", "F(T [e])"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T [e]\nU");
    assert_eq!(green.to_string(), "T [e]");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn leading_bracket_row_head_is_mandatory_at_normal_boundaries() {
    for source in ["[e]", "F([e])"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("[e]\nT");
    assert_eq!(green.to_string(), "[e]");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn leading_bracket_row_retries_a_balanced_second_row_as_one_error() {
    for source in ["[e][f]T", "[e][/*]*/f]T"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let top = top_type_expression(&green);
        assert_eq!(
            top.descendants()
                .filter(|node| node.kind() == SyntaxKind::BracketRow)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            top.children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("[e][f");
    assert_eq!(green.to_string(), "[e]");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );
}

#[test]
fn leading_bracket_row_retries_malformed_heads_without_a_missing_cascade() {
    for source in ["[e] @ T", "[e] @"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let top = top_type_expression(&green);
        assert_eq!(
            top.children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !top.children()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
        assert!(
            top.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Whitespace)
                .all(|token| token
                    .parent()
                    .is_some_and(|parent| parent.kind() == SyntaxKind::TypeExpression)),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("[e] @\nT");
    assert_eq!(green.to_string(), "[e] @");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert!(
        !top_type_expression(&green)
            .children()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn bracket_rows_recover_malformed_items_and_local_closes() {
    for (source, missing) in [
        ("T [)] -> U", 1),
        ("T [e)] -> U", 0),
        ("T [@ A] -> U", 0),
        ("T [@] -> U", 0),
        ("T [@", 2),
        ("T [e)", 2),
        ("T [@, A] -> U", 0),
        ("T [e @ A] -> U", 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T [@ A] -> U");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let error = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("bracket item error");
    assert_eq!(error.text().to_string(), "@ ");

    let (green, exit) = run_type("[e");
    assert_eq!(green.to_string(), "[e");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );

    let (green, exit) = run_type("T [e\n  @]");
    assert_eq!(green.to_string(), "T [e");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    let root = SyntaxNode::new_root(green);
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn bracket_row_recovery_keeps_item_and_close_slots_distinct() {
    for (source, error_text, missing) in [
        ("T [:] -> U", ":", 0),
        ("T [@\nA] -> U", "@", 0),
        ("T [@\n  A] -> U", "@\n  ", 0),
        ("T [A\n  )] -> U", ")", 0),
        ("T [@/* comment */A] -> U", "@/* comment */", 0),
        ("T [@/*\n*/A] -> U", "@/*\n*/", 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let errors = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{source:?}");
        assert_eq!(errors[0].text().to_string(), error_text, "{source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T [A\n  ] -> U");
    assert_eq!(green.to_string(), "T [A\n  ] -> U");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
    );

    let (green, exit) = run_type("T [");
    assert_eq!(green.to_string(), "T [");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        3
    );

    for (source, errors, missing) in [
        ("T [e,)] -> U", 1, 1),
        ("T [@,)] -> U", 2, 1),
        ("T [e))] -> U", 2, 0),
        ("T [e))", 2, 2),
        ("T [)", 1, 3),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            errors,
            "{source:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    for (source, parsed) in [("T [e) U]", "T [e)"), ("T [e)\nU]", "T [e)")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), parsed, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Left(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T [e)\n");
    assert_eq!(green.to_string(), "T [e)\n");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let newline = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::Newline)
        .expect("caller newline");
    assert_ne!(
        newline.parent().expect("newline parent").kind(),
        SyntaxKind::BracketRow
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );
}

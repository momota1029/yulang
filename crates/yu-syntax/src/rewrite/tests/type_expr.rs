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
            false,
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

fn assert_outer_parenthesized_close(source: &str) {
    let close_at = source.find('}').expect("outer right brace");
    let (green, exit, records) = run_type_with_recoveries(source, None);
    assert_eq!(green.to_string(), source, "{source:?}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
    assert_eq!(
        records
            .iter()
            .filter(|record| {
                record.site.role
                    == (GrammarRole::ClosingDelimiter {
                        owner: ConstructRole::ParenthesizedTypeGroup,
                        delimiter: Delimiter::Parenthesis,
                    })
            })
            .cloned()
            .collect::<Vec<_>>(),
        [expected_parenthesized_close(1, close_at)],
        "{source:?}"
    );
    assert_eq!(
        parenthesized_group(&green)
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1,
        "{source:?}"
    );
}

fn assert_local_parenthesized_close(source: &str, emitted: &str) {
    let (green, exit, remainder, records) =
        run_type_normalized_with_recoveries(source, 0, LineEntry::InLine, None, None);
    assert_eq!(green.to_string(), emitted, "{source:?}");
    let Some(NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine)) = exit else {
        panic!("local mismatched close must remain pending: {source:?}")
    };
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::RBracket));
    assert!(item.leading_view().is_grammar_empty());
    assert_eq!(remainder, "");
    assert!(records.is_empty());
    assert!(
        !parenthesized_group(&green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
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
            "A:: with",
            super::super::type_expr::TypeOuterBoundary::WITH,
            false,
            None,
        );
    assert!(primary_found);
    let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) = exit else {
        panic!("outer WITH remains pending")
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
    assert_eq!(pending.payload_view().spelling(), Some("with"));
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
fn type_call_t3a_missing_phase_preserves_outer_and_caller_boundaries_atomically() {
    for (source, emitted, pending_leading, expected) in [
        (
            "T(with",
            "T(",
            "",
            vec![
                expected_type_expression_missing(0, TypeRole::CallArgument, 2),
                expected_type_call_close(1, 2),
            ],
        ),
        ("T(A with", "T(A", " ", vec![expected_type_call_close(0, 3)]),
        (
            "T(A, with",
            "T(A,",
            " ",
            vec![
                expected_type_expression_missing(0, TypeRole::CallArgument, 4),
                expected_type_call_close(1, 4),
            ],
        ),
    ] {
        let (green, exit, primary_found, _, _, records, _, _) =
            run_required_type_with_outer_boundary_and_recoveries(
                source,
                super::super::type_expr::TypeOuterBoundary::WITH,
                false,
                None,
            );
        assert!(primary_found, "{source:?}");
        let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) = exit
        else {
            panic!("outer boundary remains pending: {source:?}")
        };
        assert_eq!(green.to_string(), emitted, "{source:?}");
        assert_eq!(
            pending.payload_view().spelling(),
            Some("with"),
            "{source:?}"
        );
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            pending_leading,
            "{source:?}",
        );
        assert_eq!(records, expected, "{source:?}");
    }

    let operators = OperatorTable::empty();
    let active_close_stops = stops_for(TokenKind::RBracket)
        & !super::super::operator::STOP_COMMA
        & !super::super::operator::STOP_SEMICOLON;
    for (source, emitted, expected) in [
        (
            "T( ] tail",
            "T(",
            vec![
                expected_type_expression_missing(0, TypeRole::CallArgument, 2),
                expected_type_call_close(1, 2),
            ],
        ),
        ("T(A ] tail", "T(A", vec![expected_type_call_close(0, 3)]),
        (
            "T(A, ] tail",
            "T(A,",
            vec![
                expected_type_expression_missing(0, TypeRole::CallArgument, 4),
                expected_type_call_close(1, 4),
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
        assert_eq!(emit_pending_leading_text(&mut pending), " ", "{source:?}");
        assert_eq!(input, " tail", "{source:?}");
        assert_eq!(records, expected, "{source:?}");
    }
}

#[test]
fn type_call_t3b_error_retry_preserves_call_boundaries_before_leading_emission() {
    for (source, emitted, error_range, close_at) in [
        ("T(@ with", "T(@", 2..3, 3),
        ("T(A,@ with", "T(A,@", 4..5, 5),
    ] {
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
        let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) = exit
        else {
            panic!("outer boundary remains pending after Call error: {source:?}")
        };
        assert_eq!(green.to_string(), emitted, "{source:?}");
        assert_eq!(
            pending.payload_view().spelling(),
            Some("with"),
            "{source:?}"
        );
        assert_eq!(emit_pending_leading_text(&mut pending), " ", "{source:?}");
        assert_eq!(records, expected, "{source:?}");
        let root = SyntaxNode::new_root(green.clone());
        let error = root
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
        let (frozen_green, frozen_exit, _, _, _, frozen_records, _, _) =
            run_required_type_with_outer_boundary_and_recoveries(
                source,
                super::super::type_expr::TypeOuterBoundary::WITH,
                false,
                Some(&frozen),
            );
        let NormalizedExit::Complete(Err(Either::Left(mut frozen_pending)), LineEntry::InLine) =
            frozen_exit
        else {
            panic!("frozen outer boundary remains pending after Call error: {source:?}")
        };
        assert_eq!(frozen_green, green, "{source:?}");
        assert_eq!(
            frozen_pending.payload_view().spelling(),
            Some("with"),
            "{source:?}",
        );
        assert_eq!(
            emit_pending_leading_text(&mut frozen_pending),
            " ",
            "{source:?}",
        );
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
fn type_call_t3b_close_error_stops_before_caller_and_outer_boundaries() {
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
    let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) = exit else {
        panic!("outer WITH remains pending after local Call mismatch")
    };
    assert_eq!(green.to_string(), "T(A] @");
    assert_eq!(pending.payload_view().spelling(), Some("with"));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");
    assert_eq!(
        records,
        [
            expected_type_call_close_error(0, 3..4),
            expected_type_call_close_error(1, 5..6),
            expected_type_call_close(2, 6),
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
    let NormalizedExit::Complete(Err(Either::Left(mut frozen_pending)), LineEntry::InLine) =
        frozen_exit
    else {
        panic!("frozen outer WITH remains pending after local Call malformed content")
    };
    assert_eq!(frozen_green, green);
    assert_eq!(frozen_pending.payload_view().spelling(), Some("with"));
    assert_eq!(emit_pending_leading_text(&mut frozen_pending), " ");
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
    assert_outer_parenthesized_close(":{(}");
    assert_local_parenthesized_close("(]", "(");
}

#[test]
fn parenthesized_close_post_head() {
    assert_outer_parenthesized_close(":{(A}");
    assert_local_parenthesized_close("(A]", "(A");
}

#[test]
fn parenthesized_close_malformed_retry() {
    assert_outer_parenthesized_close(":{(@}");
    assert_local_parenthesized_close("(@]", "(@");
}

#[test]
fn parenthesized_close_after_separator() {
    assert_outer_parenthesized_close(":{(A,}");
    assert_local_parenthesized_close("(A,]", "(A,");
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
            expected_type_error(0, TypeRole::PolymorphicVariantTagName, 2..4),
            expected_parenthesized_close(1, 4),
        ]
    );
    assert_eq!(parenthesized_group(&green).text().to_string(), "(A");
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
    assert_eq!(green.to_string(), "(A");
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
        panic!("active non-close caller boundary must remain pending")
    };
    assert_eq!(item.payload_view().spelling(), Some("with"));
    assert_eq!(item.leading_view().remaining_physical_parts(), 1);
    assert_eq!(input, "");
    assert_eq!(successor_origin, 7);
    assert_eq!(records, [expected_parenthesized_close(0, 2)]);
}

#[test]
fn parenthesized_close_active_caller_close_is_raw_and_preserves_successor() {
    let operators = OperatorTable::empty();
    let active_close_stops = stops_for(TokenKind::RBracket)
        & !super::super::operator::STOP_COMMA
        & !super::super::operator::STOP_SEMICOLON;
    for (source, emitted, missing_count) in [
        ("( ] tail", "(", 1),
        ("(A ] tail", "(A", 1),
        ("(@ ] tail", "(@", 1),
        ("(A, ] tail", "(A,", 2),
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
        let control_source = source
            .strip_prefix(emitted)
            .expect("emitted prefix belongs to source");
        let (control_item, control_origin, control_line, control_remainder, mark, same_operators) =
            scan_type_item_control(control_source, emitted.len(), &operators);
        assert_eq!(green.to_string(), emitted, "{source:?}");
        assert_eq!(
            parenthesized_group(&green)
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing_count,
            "{source:?}"
        );
        assert!(records.is_empty(), "{source:?}");
        assert_eq!(slots, 0, "{source:?}");
        assert_eq!(diagnostics, (Some(0), 0), "{source:?}");
        assert_eq!(item, control_item, "{source:?}");
        assert_eq!(
            item.payload_view().token_kind(),
            Some(TokenKind::RBracket),
            "{source:?}"
        );
        assert_eq!(item.leading_view().remaining_physical_parts(), 1);
        assert!(item.leading_view().has_ordinary_trivia());
        assert!(!item.leading_view().has_ordinary_newline());
        assert_eq!(input, control_remainder, "{source:?}");
        assert_eq!(successor_origin, control_origin, "{source:?}");
        assert_eq!(line_entry, control_line, "{source:?}");
        assert_eq!(mark, ());
        assert!(same_operators);
    }
}

#[test]
fn type_delimited_owner_routing_keeps_effect_and_bracket_close_recovery_raw() {
    for source in ["'[A", "[e"] {
        let (green, _, records) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(records.is_empty(), "{source:?}");
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
    let frozen = [expected_parenthesized_close(0, 2)];

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
        control_item,
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
    assert_eq!(candidate_item.leading_view().remaining_physical_parts(), 1);
    assert!(candidate_item.leading_view().has_ordinary_trivia());
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

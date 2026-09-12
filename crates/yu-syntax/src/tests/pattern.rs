use crate::tests::support::*;
use crate::{
    lexical::{
        current_item::{CurrentItem, LineEntry, current_item},
        expression_item::scan_pattern_literal_payload,
        item::{BorrowedTarget, Boundary},
        lexer::scan_pattern_nud_payload,
        yumark::{FenceBoundary, FenceOpener, FencePrefixPolicy},
    },
    literal::{
        PatternLiteralOpener, RuleLiteralExit, StringLiteralExit, rule_literal_witness,
        scan_pattern_literal_opener_witness, string_literal_with_virtual_statements_witness,
    },
    pattern::{
        PATTERN_STOP_COLON, PATTERN_STOP_EQUALS, PatternCallerCloses, PatternCompletion,
        PatternMandatorySlotPolicy, PatternStops, pattern_normalized,
        required_pattern_from_entry_item_with_policy_normalized,
    },
    statement::StatementLineHandoff,
};
use reborrow_generic::Reborrow as _;

mod recovery;

#[derive(Debug, Eq, PartialEq)]
pub(super) enum PatternLiteralWitnessExit {
    Rule(RuleLiteralExit),
    String(StringLiteralExit),
}

/// Applies LC-5's one-quote/three-quote split without making it reachable
/// through the same literal owners used by the production Pattern primary.
pub(super) fn pattern_literal_witness(
    mut i: SyntaxIn,
    origin: usize,
    fence: &FenceBoundary,
) -> Option<PatternLiteralWitnessExit> {
    let opener = i.token(scan_pattern_literal_opener_witness)?;
    match opener {
        PatternLiteralOpener::Rule(opener) => Some(PatternLiteralWitnessExit::Rule(
            rule_literal_witness(i, opener, origin + 1, fence),
        )),
        PatternLiteralOpener::String(opener, mode) => {
            let opener_length = opener
                .payload_view()
                .spelling()
                .expect("a Pattern string opener is one token")
                .len();
            Some(PatternLiteralWitnessExit::String(
                string_literal_with_virtual_statements_witness(
                    i,
                    opener,
                    mode,
                    origin + opener_length,
                    fence,
                ),
            ))
        }
    }
}

fn run_required_pattern_with_policy<'source>(
    source: &'source str,
    stops: PatternStops,
    policy: PatternMandatorySlotPolicy,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, NormalizedExit, PatternCompletion, &'source str) {
    run_required_pattern_with_context(
        source,
        stops,
        policy,
        PatternCallerCloses::NONE,
        item_origin,
        line_entry,
        fence,
    )
}

fn run_required_pattern_with_context<'source>(
    source: &'source str,
    stops: PatternStops,
    policy: PatternMandatorySlotPolicy,
    caller_closes: PatternCallerCloses,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, NormalizedExit, PatternCompletion, &'source str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = source;
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let CurrentItem {
        item,
        next_line_entry,
    } = current_item(
        chasa_recover::In::new(
            &mut input,
            &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
            (),
        ),
        item_origin,
        line_entry,
        fence,
        |lex, leading, origin, fence, _| {
            scan_pattern_nud_payload(lex, leading, origin, fence, stops)
        },
    )
    .expect("mandatory Pattern acquisition is total");
    let next_origin = item_origin
        .checked_add(source.len() - input.len())
        .expect("test Pattern origin");
    let (exit, completion) = required_pattern_from_entry_item_with_policy_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
        item,
        0,
        stops,
        StatementLineHandoff::OrdinaryLayout,
        policy,
        caller_closes,
        next_origin,
        next_line_entry,
        fence,
        Some(crate::ambient_claim::AmbientClaimView::root_statement(0)).into(),
    );
    builder.finish_node();
    (
        (builder.finish(), recover.finish_recoveries_for_test()).0,
        exit,
        completion,
        input,
    )
}

fn policy(fresh: PatternStops, recovered_tail: PatternStops) -> PatternMandatorySlotPolicy {
    PatternMandatorySlotPolicy {
        fresh_primary_recovery_stops: fresh,
        recovered_primary_tail_stops: recovered_tail,
    }
}

fn recovery_count(green: &GreenNode, kind: SyntaxKind) -> usize {
    if kind == SyntaxKind::Error {
        return crate::tests::recovery_output::recovery_groups(&SyntaxNode::new_root(
            green.clone(),
        ))
        .len();
    }
    SyntaxNode::new_root(green.clone())
        .descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

fn run_pattern_literal<'source>(
    source: &'source str,
) -> (GreenNode, PatternLiteralWitnessExit, &'source str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = source;
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = pattern_literal_witness(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
        0,
        &FenceBoundary {
            opener: FenceOpener {
                line: 0,
                marker: 0..0,
                marker_width: 0,
            },
            prefix_policy: FencePrefixPolicy::None,
            close_column: 0,
        },
    )
    .expect("Pattern quote witness");
    builder.finish_node();
    (finish_without_recoveries(builder, recover), exit, input)
}

fn run_l7_pattern<'source>(source: &'source str) -> (GreenNode, NormalizedExit, &'source str) {
    run_l7_pattern_with_context(source, 0, LineEntry::InLine, None)
}

fn run_l7_pattern_with_context<'source>(
    source: &'source str,
    origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, NormalizedExit, &'source str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = source;
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = pattern_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
        origin,
        line_entry,
        fence,
        0,
        Some(crate::ambient_claim::AmbientClaimView::root_statement(0)).into(),
    );
    builder.finish_node();
    (
        (builder.finish(), recover.finish_recoveries_for_test()).0,
        exit,
        input,
    )
}

fn pattern_node(green: GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("Pattern")
}

fn direct_kinds_and_ranges(node: &SyntaxNode) -> Vec<(SyntaxKind, std::ops::Range<usize>)> {
    node.children_with_tokens()
        .map(|element| {
            (
                element.kind(),
                usize::from(element.text_range().start())..usize::from(element.text_range().end()),
            )
        })
        .collect()
}

#[test]
fn pattern_initial_slots_have_direct_cst_selectors_in_their_actual_caller_shells() {
    let child = |node: &SyntaxNode, kind| {
        node.children()
            .find(|child| child.kind() == kind)
            .unwrap_or_else(|| panic!("{kind:?} child in {node:#?}"))
    };

    // Pattern(Primary): native retry leading stays a direct Pattern child, and
    // the UTF-8 retry starts at its byte coordinate.
    let (green, _) = run_pattern("@ λ");
    let primary = pattern_node(green);
    assert_eq!(
        direct_kinds_and_ranges(&primary),
        [
            (SyntaxKind::Error, 0..1),
            (SyntaxKind::Whitespace, 1..2),
            (SyntaxKind::IdentifierPattern, 2..4),
        ]
    );

    // Pattern(AlternationRhs): the second pipe is both the Missing coordinate
    // and the direct start of the nested alternation tail.
    let (green, _) = run_pattern("A | | B");
    let alternation = child(&pattern_node(green), SyntaxKind::PatternAlternationTail);
    assert_eq!(
        direct_kinds_and_ranges(&alternation),
        [
            (SyntaxKind::Pipe, 2..3),
            (SyntaxKind::Whitespace, 3..4),
            (SyntaxKind::Pattern, 4..7),
        ]
    );
    let rhs = child(&alternation, SyntaxKind::Pattern);
    assert_eq!(
        direct_kinds_and_ranges(&rhs),
        [
            (SyntaxKind::Missing, 4..4),
            (SyntaxKind::PatternAlternationTail, 4..7),
        ]
    );

    // The five delimited initial roles are selected by their real immediate
    // caller nodes, not by a recovery record or an Error token spelling.
    for (source, owner, slot_owner, at) in [
        (
            "(,a)",
            SyntaxKind::ParenthesizedPattern,
            SyntaxKind::ParenthesizedPattern,
            1,
        ),
        ("[,a]", SyntaxKind::ListPattern, SyntaxKind::ListPattern, 1),
        (
            "[..]",
            SyntaxKind::ListPattern,
            SyntaxKind::ListPatternSpreadItem,
            3,
        ),
        (
            "{a:}",
            SyntaxKind::RecordPattern,
            SyntaxKind::RecordPatternField,
            3,
        ),
        (
            "{..}",
            SyntaxKind::RecordPattern,
            SyntaxKind::RecordPatternSpreadItem,
            3,
        ),
    ] {
        let (green, _) = run_pattern(source);
        let owner_node = child(&pattern_node(green), owner);
        let immediate = if slot_owner == owner {
            owner_node
        } else {
            child(&owner_node, slot_owner)
        };
        let slot = child(&immediate, SyntaxKind::Pattern);
        assert_eq!(
            direct_kinds_and_ranges(&slot),
            [(SyntaxKind::Missing, at..at)],
            "{source}"
        );
    }

    // Binding(Target), including its direct Equals-boundary bypass, retains a
    // Pattern wrapper. The retry and boundary forms use the same selector.
    let (green, _) = run_statement("my @ x = value");
    let binding = |green: GreenNode| {
        SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BindingStatement)
            .unwrap()
    };
    let header = child(
        &child(&binding(green), SyntaxKind::BindingHeader),
        SyntaxKind::Pattern,
    );
    assert_eq!(
        direct_kinds_and_ranges(&header),
        [
            (SyntaxKind::Error, 3..4),
            (SyntaxKind::Whitespace, 4..5),
            (SyntaxKind::IdentifierPattern, 5..6),
        ]
    );
    let (green, _) = run_statement("my = value");
    let header = child(
        &child(&binding(green), SyntaxKind::BindingHeader),
        SyntaxKind::Pattern,
    );
    assert_eq!(
        direct_kinds_and_ranges(&header),
        [(SyntaxKind::Missing, 3..3)]
    );

    // ForStatement(Pattern) and CaseLike(Pattern) keep retry leading directly
    // under their selected Pattern child.
    let (green, _) = run_statement("for @ x in xs: body");
    let pattern = child(
        &SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForStatement)
            .unwrap(),
        SyntaxKind::Pattern,
    );
    assert_eq!(
        direct_kinds_and_ranges(&pattern),
        [
            (SyntaxKind::Error, 4..5),
            (SyntaxKind::Whitespace, 5..6),
            (SyntaxKind::IdentifierPattern, 6..7),
        ]
    );
    let (green, _) = run_statement("case x: @ arm -> body");
    let arm = child(
        &child(
            &child(
                &SyntaxNode::new_root(green)
                    .descendants()
                    .find(|node| node.kind() == SyntaxKind::CaseExpression)
                    .unwrap(),
                SyntaxKind::CaseBlock,
            ),
            SyntaxKind::CaseArm,
        ),
        SyntaxKind::Pattern,
    );
    assert_eq!(
        direct_kinds_and_ranges(&arm),
        [
            (SyntaxKind::Error, 8..9),
            (SyntaxKind::Whitespace, 9..10),
            (SyntaxKind::IdentifierPattern, 10..13),
        ]
    );

    // CaseLike(Handler): the native comma precedes its second Pattern child;
    // its initial gap remains in the existing Error topology.
    let (green, _) = run_statement("catch x: err, @ handler -> body");
    let catch_arm = child(
        &child(
            &SyntaxNode::new_root(green)
                .descendants()
                .find(|node| node.kind() == SyntaxKind::CatchExpression)
                .unwrap(),
            SyntaxKind::CatchBlock,
        ),
        SyntaxKind::CatchArm,
    );
    assert_eq!(
        direct_kinds_and_ranges(&catch_arm)[..3],
        [
            (SyntaxKind::Pattern, 9..12),
            (SyntaxKind::Comma, 12..13),
            (SyntaxKind::Pattern, 13..23),
        ]
    );
    let arm = catch_arm
        .children()
        .filter(|node| node.kind() == SyntaxKind::Pattern)
        .nth(1)
        .expect("handler Pattern after the native comma");
    assert_eq!(
        direct_kinds_and_ranges(&arm),
        [
            (SyntaxKind::Error, 13..14),
            (SyntaxKind::Error, 14..15),
            (SyntaxKind::Whitespace, 15..16),
            (SyntaxKind::IdentifierPattern, 16..23),
        ]
    );
}

#[test]
fn pattern_initial_delimited_errors_end_before_close_or_native_retry_leading() {
    use SyntaxKind::*;
    for (prefix, suffix, owner, nested_owner) in [
        ("(", ")", ParenthesizedPattern, None),
        ("[", "]", ListPattern, None),
        ("[..", "]", ListPattern, Some(ListPatternSpreadItem)),
        ("{a:", "}", RecordPattern, Some(RecordPatternField)),
        ("{..", "}", RecordPattern, Some(RecordPatternSpreadItem)),
    ] {
        for retry in ["", " x"] {
            let source = format!("{prefix}@{retry}{suffix}");
            let (green, _) = run_pattern(&source);
            let outer = pattern_node(green)
                .children()
                .find(|node| node.kind() == owner)
                .expect("actual delimiter caller");
            let immediate = nested_owner.map_or_else(
                || outer.clone(),
                |kind| outer.children().find(|node| node.kind() == kind).unwrap(),
            );
            let slot = immediate
                .children()
                .find(|node| node.kind() == Pattern)
                .unwrap();
            let at = prefix.len();
            let mut expected = vec![(Error, at..at + 1)];
            if !retry.is_empty() {
                expected.extend([
                    (Whitespace, at + 1..at + 2),
                    (IdentifierPattern, at + 2..at + 3),
                ]);
            }
            assert_eq!(direct_kinds_and_ranges(&slot), expected, "{source}");
            // The close is emitted by the caller, never swallowed by Error.
            let close = outer.last_token().unwrap();
            assert_eq!(
                usize::from(close.text_range().start()),
                source.len() - 1,
                "{source}"
            );
            assert_eq!(close.text(), suffix, "{source}");
        }
    }
}

#[test]
fn pattern_initial_statement_slots_cover_missing_terminal_error_and_retry() {
    use SyntaxKind::*;
    // Selector is the direct Pattern ordinal in its real immediate caller.
    // In particular CatchArm's second Pattern is after the native comma.
    for (prefix, suffix, owner, ordinal) in [
        ("my ", "= value", BindingHeader, 0),
        ("for ", "in xs: body", ForStatement, 0),
        ("case x: ", "-> body", CaseArm, 0),
        ("catch x: ", "-> body", CatchArm, 0),
        ("catch x: err,", "-> body", CatchArm, 1),
    ] {
        for initial in ["", "@ ", "@ x "] {
            let source = format!("{prefix}{initial}{suffix}");
            let (green, exit) = run_statement(&source);
            let root = SyntaxNode::new_root(green);
            let caller = root
                .descendants()
                .find(|node| node.kind() == owner)
                .unwrap();
            let slot = caller
                .children()
                .filter(|node| node.kind() == Pattern)
                .nth(ordinal)
                .unwrap();
            let at = prefix.len();
            let expected = match initial {
                "" => {
                    let missing_at = if owner == ForStatement { at - 1 } else { at };
                    vec![(Missing, missing_at..missing_at)]
                }
                "@ " => vec![(Error, at..at + 1)],
                "@ x " => vec![
                    (Error, at..at + 1),
                    (Whitespace, at + 1..at + 2),
                    (IdentifierPattern, at + 2..at + 3),
                ],
                _ => unreachable!(),
            };
            assert_eq!(direct_kinds_and_ranges(&slot), expected, "{source}");
            if ordinal == 1 {
                let comma = slot.prev_sibling_or_token().expect("native handler comma");
                assert_eq!(comma.kind(), Comma, "{source}");
                assert_eq!(usize::from(comma.text_range().end()), at, "{source}");
            }
            // The caller resumes at its protected delimiter/word after the
            // initial slot; the Error cannot own any of that payload.
            let boundary_at = prefix.len() + initial.len();
            if owner == ForStatement && initial == "@ " {
                let Some(Err(Either::Left(mut item))) = exit else {
                    panic!("terminal For Pattern leaves in pending");
                };
                assert_eq!(
                    item.payload_view().token_kind(),
                    Some(TokenKind::Identifier)
                );
                assert_eq!(item.payload_view().spelling(), Some("in"));
                assert_eq!(emit_pending_leading_text(&mut item), " ");
                assert_eq!(usize::from(slot.text_range().end()), boundary_at - 1);
                continue;
            }
            assert!(
                root.descendants_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(
                        |token| usize::from(token.text_range().start()) == boundary_at
                            && token.kind() != Error
                    ),
                "{source}"
            );
        }
    }
}

#[test]
fn pattern_initial_primary_and_alternation_keep_nested_owners_distinct() {
    use SyntaxKind::*;
    let (green, _) = run_pattern("");
    assert_eq!(
        direct_kinds_and_ranges(&pattern_node(green)),
        [(Missing, 0..0)]
    );
    for (source, expected) in [
        ("A | @", vec![(Error, 4..5)]),
        (
            "A | @ x",
            vec![(Error, 4..5), (Whitespace, 5..6), (IdentifierPattern, 6..7)],
        ),
        ("A | @ :", vec![(Error, 4..5)]),
    ] {
        let (green, _) = run_pattern(source);
        let outer = pattern_node(green);
        let tail = outer
            .children()
            .find(|node| node.kind() == PatternAlternationTail)
            .unwrap();
        let rhs = tail.children().find(|node| node.kind() == Pattern).unwrap();
        assert_eq!(direct_kinds_and_ranges(&rhs), expected, "{source}");
        if source.ends_with(':') {
            let annotation = outer
                .children()
                .find(|node| node.kind() == PatternTypeAnnotation)
                .unwrap();
            assert!(annotation.text_range().start() >= tail.text_range().end());
            assert!(annotation.descendants().any(|node| node.kind() == Missing));
            assert!(!rhs.children().any(|node| node.kind() == Missing));
        }
    }
    // Accepted delimiter children delegate symbol/alias absence to their
    // nested owner; neither is an initial Pattern Missing.
    for (source, nested) in [("[: ]", SymbolPattern), ("[x as ]", PatternAliasTail)] {
        let (green, _) = run_pattern(source);
        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == nested)
            .unwrap();
        assert!(
            owner.children().any(|node| node.kind() == Missing),
            "{source}"
        );
        assert!(
            !owner
                .parent()
                .unwrap()
                .children()
                .any(|node| node.kind() == Missing),
            "{source}"
        );
    }
}

#[test]
fn pattern_initial_direct_cst_controls_keep_stops_crlf_and_fences_pending() {
    let (green, exit) = run_pattern_with_colon_stop("@ :", true);
    assert_eq!(
        direct_kinds_and_ranges(&pattern_node(green)),
        [(SyntaxKind::Error, 0..1)]
    );
    let Err(Either::Left(mut stop)) = exit else {
        panic!("colon stop remains pending");
    };
    assert_eq!(token_kind(&stop), Some(TokenKind::Colon));
    assert_eq!(emit_pending_leading_text(&mut stop), " ");

    let (green, exit) = run_pattern("@\r\nλ");
    assert_eq!(
        direct_kinds_and_ranges(&pattern_node(green)),
        [(SyntaxKind::Error, 0..1)]
    );
    let Err(Either::Left(mut retry)) = exit else {
        panic!("CRLF retry remains pending");
    };
    assert_eq!(token_kind(&retry), Some(TokenKind::Identifier));
    assert_eq!(emit_pending_leading_text(&mut retry), "\r\n");

    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let (green, exit, _, _) = run_required_pattern_with_context(
        "@\r\n> > ```",
        PATTERN_DEFAULT_STOPS,
        PatternMandatorySlotPolicy::default(),
        PatternCallerCloses::NONE,
        100,
        LineEntry::InLine,
        Some(&fence),
    );
    assert_eq!(
        direct_kinds_and_ranges(&pattern_node(green)),
        [(SyntaxKind::Error, 0..1)]
    );
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart)
            if item.payload_view().is_boundary()
    ));
}

fn record_node(green: GreenNode) -> SyntaxNode {
    pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::RecordPattern)
        .expect("RecordPattern")
}

fn annotation_node(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
        .expect("PatternTypeAnnotation")
}

#[test]
fn mandatory_pattern_policy_reserves_only_fresh_primary_recovery_stops() {
    let fresh_stops = PATTERN_STOP_COLON | PATTERN_STOP_EQUALS;
    for (source, kind, remainder) in [
        (": T", TokenKind::Colon, " T"),
        ("= value", TokenKind::Equals, " value"),
    ] {
        let (green, exit, completion, actual_remainder) = run_required_pattern_with_policy(
            source,
            0,
            policy(fresh_stops, 0),
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), "", "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        assert_eq!(completion, PatternCompletion::Incomplete, "{source:?}");
        assert_eq!(recovery_count(&green, SyntaxKind::Missing), 1);
        assert_eq!(recovery_count(&green, SyntaxKind::Error), 0);
        let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
            panic!("fresh stop Item must remain pending: {source:?}")
        };
        assert_eq!(item.payload_view().token_kind(), Some(kind), "{source:?}");
    }

    for (source, kind) in [("@ :", TokenKind::Colon), ("@ =", TokenKind::Equals)] {
        let (green, exit, completion, remainder) = run_required_pattern_with_policy(
            source,
            0,
            policy(fresh_stops, 0),
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), "@", "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        assert_eq!(completion, PatternCompletion::Incomplete, "{source:?}");
        assert_eq!(recovery_count(&green, SyntaxKind::Error), 1);
        assert_eq!(recovery_count(&green, SyntaxKind::Missing), 0);
        let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit else {
            panic!("recovery stop Item must remain pending: {source:?}")
        };
        assert_eq!(item.payload_view().token_kind(), Some(kind), "{source:?}");
        assert_eq!(emit_pending_leading_text(&mut item), " ", "{source:?}");
    }

    for source in [":symbol", "x: T", "{x = 1}", "@ x: T", "@ {x = 1}"] {
        let (green, _, completion, remainder) = run_required_pattern_with_policy(
            source,
            0,
            policy(fresh_stops, 0),
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        assert_eq!(completion, PatternCompletion::Complete, "{source:?}");
        assert_eq!(recovery_count(&green, SyntaxKind::Missing), 0, "{source:?}");
    }
    let symbol = run_required_pattern_with_policy(
        ":symbol",
        0,
        policy(fresh_stops, 0),
        0,
        LineEntry::InLine,
        None,
    )
    .0;
    assert_eq!(
        SyntaxNode::new_root(symbol)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::SymbolPattern)
            .count(),
        1
    );
}

#[test]
fn mandatory_pattern_policy_reserves_only_recovered_parenthesized_primary_tail() {
    let source = "(x @): T";
    let (default_green, _, default_completion, default_remainder) =
        run_required_pattern_with_policy(
            source,
            0,
            PatternMandatorySlotPolicy::default(),
            0,
            LineEntry::InLine,
            None,
        );
    assert_eq!(default_green.to_string(), source);
    assert_eq!(default_remainder, "");
    assert_eq!(default_completion, PatternCompletion::Complete);
    assert_eq!(recovery_count(&default_green, SyntaxKind::Error), 1);
    assert_eq!(
        SyntaxNode::new_root(default_green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
            .count(),
        1
    );

    let (green, exit, completion, remainder) = run_required_pattern_with_policy(
        source,
        0,
        policy(0, PATTERN_STOP_COLON),
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "(x @)");
    assert_eq!(remainder, " T");
    assert_eq!(completion, PatternCompletion::Complete);
    assert_eq!(recovery_count(&green, SyntaxKind::Error), 1);
    assert_eq!(recovery_count(&green, SyntaxKind::Missing), 0);
    assert_eq!(
        SyntaxNode::new_root(green.clone())
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
            .count(),
        0
    );
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
        panic!("recovered Parenthesized Pattern must return the colon pending")
    };
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Colon));

    for nested in ["((x @): T)", "(@ (x @)): T"] {
        let (green, _, completion, remainder) = run_required_pattern_with_policy(
            nested,
            0,
            policy(PATTERN_STOP_COLON | PATTERN_STOP_EQUALS, PATTERN_STOP_COLON),
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), nested, "{nested:?}");
        assert_eq!(remainder, "", "{nested:?}");
        assert_eq!(completion, PatternCompletion::Complete, "{nested:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::PatternTypeAnnotation),
            "{nested:?}"
        );
    }
}

#[test]
fn mandatory_pattern_policy_preserves_fenced_boundaries_and_coordinates() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let origin = 8_000;
    let source = "@\r\n> > ```\r\nouter";
    let (green, exit, completion, remainder) = run_required_pattern_with_policy(
        source,
        0,
        policy(PATTERN_STOP_COLON | PATTERN_STOP_EQUALS, PATTERN_STOP_COLON),
        origin,
        LineEntry::InLine,
        Some(&fence),
    );
    assert_eq!(green.to_string(), "@");
    assert_eq!(remainder, "> > ```\r\nouter");
    assert_eq!(completion, PatternCompletion::Incomplete);
    assert_eq!(recovery_count(&green, SyntaxKind::Error), 1);
    assert_eq!(recovery_count(&green, SyntaxKind::Missing), 0);
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart) = exit else {
        panic!("fenced close must remain the pending Pattern boundary")
    };
    let (leading, pending) = emit_terminal_leading_text(item);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + 3);
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));
}

#[test]
fn pattern_caller_closes_keep_own_close_first_and_return_outer_close_unchanged() {
    for (source, caller_closes, close, green_text, expected_missing, expected_completion) in [
        (
            "(x)) tail",
            PatternCallerCloses::RPAREN,
            TokenKind::RParen,
            "(x)",
            0,
            PatternCompletion::Complete,
        ),
        (
            "[x ) tail",
            PatternCallerCloses::RPAREN,
            TokenKind::RParen,
            "[x",
            1,
            PatternCompletion::Incomplete,
        ),
        (
            "{x ) tail",
            PatternCallerCloses::RPAREN,
            TokenKind::RParen,
            "{x",
            1,
            PatternCompletion::Incomplete,
        ),
        (
            "(x ] tail",
            PatternCallerCloses::RBRACKET,
            TokenKind::RBracket,
            "(x",
            1,
            PatternCompletion::Incomplete,
        ),
        (
            "(x } tail",
            PatternCallerCloses::RBRACE,
            TokenKind::RBrace,
            "(x",
            1,
            PatternCompletion::Incomplete,
        ),
    ] {
        let (green, exit, completion, remainder) = run_required_pattern_with_context(
            source,
            0,
            PatternMandatorySlotPolicy::default(),
            caller_closes,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), green_text, "{source:?}");
        assert_eq!(remainder, " tail", "{source:?}");
        assert_eq!(completion, expected_completion, "{source:?}");
        assert_eq!(
            recovery_count(&green, SyntaxKind::Missing),
            expected_missing
        );
        assert_eq!(recovery_count(&green, SyntaxKind::Error), 0, "{source:?}");
        let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit else {
            panic!("caller close must remain pending: {source:?}")
        };
        assert_eq!(item.payload_view().token_kind(), Some(close), "{source:?}");
        let expected_leading = if source.contains("x ") { " " } else { "" };
        assert_eq!(
            emit_pending_leading_text(&mut item),
            expected_leading,
            "{source:?}"
        );
    }
}

#[test]
fn pattern_caller_closes_flow_through_nested_patterns_and_recovery() {
    for (source, expected_errors) in [("((x))", 0), ("((x @))", 1)] {
        let (green, exit, completion, remainder) = run_required_pattern_with_context(
            source,
            0,
            PatternMandatorySlotPolicy::default(),
            PatternCallerCloses::NONE,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        assert_eq!(completion, PatternCompletion::Complete, "{source:?}");
        assert_eq!(recovery_count(&green, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(
            recovery_count(&green, SyntaxKind::Error),
            expected_errors,
            "{source:?}"
        );
        assert!(
            matches!(exit, NormalizedExit::Complete(Err(Either::Right(_)), _)),
            "{source:?}"
        );
    }

    for (source, expected_missing) in [
        ("[x | y) tail", 1),
        ("[..x) tail", 1),
        ("{field: [x) tail", 2),
        ("{..[x) tail", 2),
    ] {
        let (green, exit, _, remainder) = run_required_pattern_with_context(
            source,
            0,
            PatternMandatorySlotPolicy::default(),
            PatternCallerCloses::RPAREN,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(remainder, " tail", "{source:?}");
        assert_eq!(
            recovery_count(&green, SyntaxKind::Missing),
            expected_missing
        );
        assert_eq!(recovery_count(&green, SyntaxKind::Error), 0, "{source:?}");
        let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
            panic!("nested caller close must remain pending: {source:?}")
        };
        assert_eq!(
            item.payload_view().token_kind(),
            Some(TokenKind::RParen),
            "{source:?}"
        );
    }
}

#[test]
fn pattern_caller_close_matrix_preserves_recursive_frontiers_and_composed_bits() {
    let all_closes = PatternCallerCloses::RPAREN
        .union(PatternCallerCloses::RBRACKET)
        .union(PatternCallerCloses::RBRACE);
    assert_eq!(
        all_closes,
        PatternCallerCloses::RBRACE
            .union(PatternCallerCloses::RPAREN)
            .union(PatternCallerCloses::RBRACKET)
    );

    for (
        source,
        caller_closes,
        owner_kind,
        close,
        green_text,
        expected_owner_missing,
        expected_total_missing,
    ) in [
        (
            "[x | ) tail",
            PatternCallerCloses::RPAREN,
            SyntaxKind::ListPattern,
            TokenKind::RParen,
            "[x |",
            1,
            2,
        ),
        (
            "[.. ) tail",
            PatternCallerCloses::RPAREN,
            SyntaxKind::ListPattern,
            TokenKind::RParen,
            "[..",
            1,
            2,
        ),
        (
            "[.. } tail",
            PatternCallerCloses::RPAREN.union(PatternCallerCloses::RBRACE),
            SyntaxKind::ListPattern,
            TokenKind::RBrace,
            "[..",
            1,
            2,
        ),
        (
            "[(x ] ] tail",
            PatternCallerCloses::RPAREN.union(PatternCallerCloses::RBRACKET),
            SyntaxKind::ListPattern,
            TokenKind::RBracket,
            "[(x ]",
            0,
            1,
        ),
        (
            "{.. ) tail",
            PatternCallerCloses::RPAREN,
            SyntaxKind::RecordPattern,
            TokenKind::RParen,
            "{..",
            1,
            2,
        ),
        (
            "{field: ) tail",
            PatternCallerCloses::RPAREN,
            SyntaxKind::RecordPattern,
            TokenKind::RParen,
            "{field:",
            1,
            2,
        ),
        (
            "{field: ] tail",
            PatternCallerCloses::RPAREN.union(PatternCallerCloses::RBRACKET),
            SyntaxKind::RecordPattern,
            TokenKind::RBracket,
            "{field:",
            1,
            2,
        ),
        (
            "{field: (x } } tail",
            PatternCallerCloses::RPAREN.union(PatternCallerCloses::RBRACE),
            SyntaxKind::RecordPattern,
            TokenKind::RBrace,
            "{field: (x }",
            0,
            1,
        ),
    ] {
        let (green, exit, _, remainder) = run_required_pattern_with_context(
            source,
            0,
            PatternMandatorySlotPolicy::default(),
            caller_closes,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), green_text, "{source:?}");
        assert_eq!(remainder, " tail", "{source:?}");
        assert_eq!(
            recovery_count(&green, SyntaxKind::Missing),
            expected_total_missing,
            "{source:?}"
        );
        assert_eq!(recovery_count(&green, SyntaxKind::Error), 0, "{source:?}");
        let owner = SyntaxNode::new_root(green.clone())
            .descendants()
            .find(|node| node.kind() == owner_kind)
            .expect("Pattern delimiter owner");
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected_owner_missing,
            "{source:?}"
        );
        let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit else {
            panic!("composed caller close must remain pending: {source:?}")
        };
        assert_eq!(item.payload_view().token_kind(), Some(close), "{source:?}");
        assert_eq!(emit_pending_leading_text(&mut item), " ", "{source:?}");
    }
}

#[test]
fn pattern_caller_closes_map_to_annotation_type_without_leaking_other_stops() {
    let source = "x: '[A) tail";
    let (green, exit, completion, remainder) = run_required_pattern_with_context(
        source,
        0,
        PatternMandatorySlotPolicy::default(),
        PatternCallerCloses::RPAREN,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "x: '[A");
    assert_eq!(remainder, " tail");
    assert_eq!(completion, PatternCompletion::Complete);
    assert_eq!(recovery_count(&green, SyntaxKind::Missing), 1);
    assert_eq!(recovery_count(&green, SyntaxKind::Error), 0);
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
        panic!("annotation Type must return the Pattern caller close")
    };
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::RParen));

    let source = "x: ) tail";
    let (green, exit, _, remainder) = run_required_pattern_with_context(
        source,
        0,
        PatternMandatorySlotPolicy::default(),
        PatternCallerCloses::RPAREN,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "x:");
    assert_eq!(remainder, " tail");
    assert_eq!(recovery_count(&green, SyntaxKind::Missing), 1);
    let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit else {
        panic!("missing annotation Type must preserve the caller close")
    };
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::RParen));
    assert_eq!(emit_pending_leading_text(&mut item), " ");

    for source in ["[x: T]", "{x = 1}"] {
        let (green, exit, completion, remainder) = run_required_pattern_with_context(
            source,
            PATTERN_STOP_COLON | PATTERN_STOP_EQUALS,
            PatternMandatorySlotPolicy::default(),
            PatternCallerCloses::NONE,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        assert_eq!(completion, PatternCompletion::Complete, "{source:?}");
        assert!(
            matches!(exit, NormalizedExit::Complete(Err(Either::Right(_)), _)),
            "{source:?}"
        );
    }

    let source = "(a]";
    let (green, _, completion, remainder) = run_required_pattern_with_context(
        source,
        0,
        PatternMandatorySlotPolicy::default(),
        PatternCallerCloses::NONE,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    assert_eq!(completion, PatternCompletion::Incomplete);
    assert_eq!(recovery_count(&green, SyntaxKind::Missing), 1);
    assert_eq!(recovery_count(&green, SyntaxKind::Error), 1);
}

#[test]
fn pattern_annotation_type_caller_close_matrix_owns_horizontal_gap() {
    for (source, caller_closes, close, green_text) in [
        (
            "x: '[A ) tail",
            PatternCallerCloses::RPAREN,
            TokenKind::RParen,
            "x: '[A ",
        ),
        (
            "x: (A ] tail",
            PatternCallerCloses::RPAREN.union(PatternCallerCloses::RBRACKET),
            TokenKind::RBracket,
            "x: (A ",
        ),
        (
            "x: '[A } tail",
            PatternCallerCloses::RPAREN.union(PatternCallerCloses::RBRACE),
            TokenKind::RBrace,
            "x: '[A ",
        ),
    ] {
        let (green, exit, completion, remainder) = run_required_pattern_with_context(
            source,
            0,
            PatternMandatorySlotPolicy::default(),
            caller_closes,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), green_text, "{source:?}");
        assert_eq!(remainder, " tail", "{source:?}");
        assert_eq!(completion, PatternCompletion::Complete, "{source:?}");
        assert_eq!(recovery_count(&green, SyntaxKind::Missing), 1, "{source:?}");
        assert_eq!(recovery_count(&green, SyntaxKind::Error), 0, "{source:?}");
        let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit else {
            panic!("annotation Type caller close must remain pending: {source:?}")
        };
        assert_eq!(item.payload_view().token_kind(), Some(close), "{source:?}");
        assert_eq!(emit_pending_leading_text(&mut item), "", "{source:?}");
    }
}

#[test]
fn pattern_annotation_type_caller_close_preserves_comment_bearing_gap() {
    for (source, caller_closes, close, green_text) in [
        (
            "x: '[A /*gap*/) tail",
            PatternCallerCloses::RPAREN,
            TokenKind::RParen,
            "x: '[A",
        ),
        (
            "x: (A /*gap*/] tail",
            PatternCallerCloses::RBRACKET,
            TokenKind::RBracket,
            "x: (A",
        ),
    ] {
        let (green, exit, completion, remainder) = run_required_pattern_with_context(
            source,
            0,
            PatternMandatorySlotPolicy::default(),
            caller_closes,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), green_text, "{source:?}");
        assert_eq!(remainder, " tail", "{source:?}");
        assert_eq!(completion, PatternCompletion::Complete, "{source:?}");
        assert_eq!(recovery_count(&green, SyntaxKind::Missing), 1, "{source:?}");
        assert_eq!(recovery_count(&green, SyntaxKind::Error), 0, "{source:?}");
        let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit else {
            panic!("annotation Type caller close must remain pending: {source:?}")
        };
        assert_eq!(item.payload_view().token_kind(), Some(close), "{source:?}");
        assert_eq!(
            emit_pending_leading_text(&mut item),
            " /*gap*/",
            "{source:?}"
        );
    }
}

#[test]
fn pattern_annotation_named_record_type_preserves_caller_close_frontiers() {
    for (source, green_text, expected_missing) in [
        ("x: { ) tail", "x: {", 1),
        ("x: {field ) tail", "x: {field", 2),
        ("x: {field: ) tail", "x: {field:", 2),
    ] {
        let (green, exit, completion, remainder) = run_required_pattern_with_context(
            source,
            0,
            PatternMandatorySlotPolicy::default(),
            PatternCallerCloses::RPAREN,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), green_text, "{source:?}");
        assert_eq!(remainder, " tail", "{source:?}");
        assert_eq!(completion, PatternCompletion::Complete, "{source:?}");
        assert_eq!(
            recovery_count(&green, SyntaxKind::Missing),
            expected_missing,
            "{source:?}"
        );
        assert_eq!(recovery_count(&green, SyntaxKind::Error), 0, "{source:?}");
        let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit else {
            panic!("named-record Type caller close must remain pending: {source:?}")
        };
        assert_eq!(
            item.payload_view().token_kind(),
            Some(TokenKind::RParen),
            "{source:?}"
        );
        assert_eq!(emit_pending_leading_text(&mut item), " ", "{source:?}");
    }
}

#[test]
fn pattern_annotation_named_record_type_owns_its_first_same_kind_close() {
    for (source, green_text, field_kinds) in [
        (
            "x: {field } } tail",
            "x: {field }",
            vec![SyntaxKind::Identifier, SyntaxKind::Missing],
        ),
        (
            "x: {field: } } tail",
            "x: {field: }",
            vec![
                SyntaxKind::Identifier,
                SyntaxKind::Colon,
                SyntaxKind::Missing,
            ],
        ),
    ] {
        let (green, exit, completion, remainder) = run_required_pattern_with_context(
            source,
            0,
            PatternMandatorySlotPolicy::default(),
            PatternCallerCloses::RPAREN.union(PatternCallerCloses::RBRACE),
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), green_text, "{source:?}");
        assert_eq!(remainder, " tail", "{source:?}");
        assert_eq!(completion, PatternCompletion::Complete, "{source:?}");
        assert_eq!(recovery_count(&green, SyntaxKind::Missing), 1, "{source:?}");
        assert_eq!(recovery_count(&green, SyntaxKind::Error), 0, "{source:?}");

        let root = SyntaxNode::new_root(green.clone());
        let field = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeRecordField)
            .expect("annotation named-record field");
        assert_eq!(
            field
                .children_with_tokens()
                .map(|element| element.kind())
                .collect::<Vec<_>>(),
            field_kinds,
            "{source:?}"
        );
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("annotation named-record Type");
        assert_eq!(
            record
                .children_with_tokens()
                .map(|element| element.kind())
                .collect::<Vec<_>>(),
            [
                SyntaxKind::LBrace,
                SyntaxKind::TypeRecordField,
                SyntaxKind::NamedRecordTypeClose
            ],
            "{source:?}"
        );
        assert_eq!(
            record
                .last_child()
                .unwrap()
                .children_with_tokens()
                .map(|element| element.kind())
                .collect::<Vec<_>>(),
            [SyntaxKind::Whitespace, SyntaxKind::RBrace],
            "{source:?}"
        );
        assert_eq!(
            record.last_token().map(|token| token.kind()),
            Some(SyntaxKind::RBrace),
            "{source:?}"
        );

        let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit else {
            panic!("outer caller close must remain pending: {source:?}")
        };
        assert_eq!(
            item.payload_view().token_kind(),
            Some(TokenKind::RBrace),
            "{source:?}"
        );
        assert_eq!(emit_pending_leading_text(&mut item), " ", "{source:?}");
    }
}

#[test]
fn standalone_patterns_emit_atomic_primaries_without_operator_chains() {
    for (source, child, token) in [
        ("x", SyntaxKind::IdentifierPattern, SyntaxKind::Identifier),
        ("_", SyntaxKind::IdentifierPattern, SyntaxKind::Identifier),
        (
            "_bar",
            SyntaxKind::IdentifierPattern,
            SyntaxKind::SigilIdentifier,
        ),
        (
            "$x",
            SyntaxKind::IdentifierPattern,
            SyntaxKind::SigilIdentifier,
        ),
        (
            "&x",
            SyntaxKind::IdentifierPattern,
            SyntaxKind::SigilIdentifier,
        ),
        (
            "'x",
            SyntaxKind::IdentifierPattern,
            SyntaxKind::SigilIdentifier,
        ),
        ("0", SyntaxKind::IntegerPattern, SyntaxKind::Integer),
        ("42", SyntaxKind::IntegerPattern, SyntaxKind::Integer),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let pattern = pattern_node(green);
        let primary = pattern.children().next().expect("Pattern primary");
        assert_eq!(primary.kind(), child, "{source:?}");
        assert_eq!(primary.first_token().map(|token| token.kind()), Some(token));
        assert!(
            !pattern
                .descendants()
                .any(|node| node.kind() == SyntaxKind::OperatorChain),
            "{source:?}"
        );
    }
}

#[test]
fn standalone_patterns_keep_symbols_and_parenthesized_layout_local() {
    let (green, exit) = run_pattern(":foo");
    assert_eq!(green.to_string(), ":foo");
    assert!(matches!(exit, Err(Either::Right(_))));
    let pattern = pattern_node(green);
    let symbol = pattern
        .children()
        .find(|node| node.kind() == SyntaxKind::SymbolPattern)
        .expect("SymbolPattern");
    assert_eq!(
        symbol
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Colon, SyntaxKind::Identifier]
    );

    for (source, elements) in [
        ("()", 0),
        ("(a)", 1),
        ("(a,)", 1),
        ("(a,b,)", 2),
        ("(A\nB)", 2),
        ("(\n  A\n  B\n)", 2),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let pattern = pattern_node(green);
        let parenthesized = pattern
            .children()
            .find(|node| node.kind() == SyntaxKind::ParenthesizedPattern)
            .expect("ParenthesizedPattern");
        assert_eq!(
            parenthesized
                .children()
                .filter(|node| node.kind() == SyntaxKind::Pattern)
                .count(),
            elements,
            "{source:?}"
        );
        assert!(
            !parenthesized.descendants_with_tokens().any(|node| matches!(
                node.kind(),
                SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
            )),
            "{source:?}"
        );
    }
}

#[test]
fn standalone_patterns_keep_fixed_tail_order_and_colon_handoffs() {
    let (green, exit) = run_pattern("A as x | B as c");
    assert_eq!(green.to_string(), "A as x | B as c");
    assert!(matches!(exit, Err(Either::Right(_))));
    let pattern = pattern_node(green);
    assert_eq!(
        pattern
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierPattern,
            SyntaxKind::PatternAliasTail,
            SyntaxKind::PatternAlternationTail,
        ]
    );
    let alternation = pattern
        .children()
        .find(|node| node.kind() == SyntaxKind::PatternAlternationTail)
        .expect("PatternAlternationTail");
    let rhs = alternation
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("alternation RHS");
    assert!(
        rhs.children()
            .any(|node| node.kind() == SyntaxKind::PatternAliasTail)
    );

    let (green, exit) = run_pattern_with_colon_stop(":foo: body", true);
    assert_eq!(green.to_string(), ":foo");
    assert!(matches!(
        exit,
        Err(Either::Left(item))
            if item.payload_view().token_kind() == Some(TokenKind::Colon)
    ));

    let (green, exit) = run_pattern_with_colon_stop(": body", true);
    assert_eq!(green.to_string(), "");
    assert!(matches!(
        exit,
        Err(Either::Left(item))
            if item.payload_view().token_kind() == Some(TokenKind::Colon)
    ));
}

#[test]
fn standalone_patterns_keep_list_record_and_annotation_owners_local() {
    for (source, items, spreads) in [
        ("[]", 0, 0),
        ("[a]", 1, 0),
        ("[a,b,]", 2, 0),
        ("[a\nb]", 2, 0),
        ("[..head, tail]", 2, 1),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let pattern = pattern_node(green);
        let list = pattern
            .children()
            .find(|node| node.kind() == SyntaxKind::ListPattern)
            .expect("ListPattern");
        assert_eq!(
            list.children()
                .filter(|node| {
                    matches!(
                        node.kind(),
                        SyntaxKind::Pattern | SyntaxKind::ListPatternSpreadItem
                    )
                })
                .count(),
            items,
            "{source:?}"
        );
        assert_eq!(
            list.children()
                .filter(|node| node.kind() == SyntaxKind::ListPatternSpreadItem)
                .count(),
            spreads,
            "{source:?}"
        );
        assert!(
            !list.descendants_with_tokens().any(|node| matches!(
                node.kind(),
                SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
            )),
            "{source:?}"
        );
    }

    for (source, fields, spreads) in [
        ("{}", 0, 0),
        ("{a}", 1, 0),
        ("{a: b, c = 1}", 2, 0),
        ("{..head, width: local_width}", 1, 1),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let pattern = pattern_node(green);
        let record = pattern
            .children()
            .find(|node| node.kind() == SyntaxKind::RecordPattern)
            .expect("RecordPattern");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::RecordPatternField)
                .count(),
            fields,
            "{source:?}"
        );
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::RecordPatternSpreadItem)
                .count(),
            spreads,
            "{source:?}"
        );
        assert!(
            !record.descendants_with_tokens().any(|node| matches!(
                node.kind(),
                SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
            )),
            "{source:?}"
        );
    }

    for source in ["x:Int", "A | B as c: Int", "{a: A: Inner}", "{a: A}: Outer"] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::TypeExpression),
            "{source:?}"
        );
    }

    let (green, _) = run_pattern("A | B as c: Int");
    assert_eq!(
        pattern_node(green)
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierPattern,
            SyntaxKind::PatternAlternationTail,
            SyntaxKind::PatternTypeAnnotation,
        ]
    );

    let (green, exit) = run_pattern("x: Int: Other");
    assert_eq!(green.to_string(), "x: Int");
    assert!(matches!(
        exit,
        Err(Either::Left(item))
            if item.payload_view().token_kind() == Some(TokenKind::Colon)
    ));

    let (green, exit) = run_pattern("x\n  : Int");
    assert_eq!(green.to_string(), "x\n  : Int");
    assert!(matches!(exit, Err(Either::Right(_))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
    );

    let (green, exit) = run_pattern("x\n: Int");
    assert_eq!(green.to_string(), "x");
    assert!(matches!(
        exit,
        Err(Either::Left(item))
            if item.payload_view().token_kind() == Some(TokenKind::Colon)
                && item.leading_view().has_ordinary_newline()
    ));
}

#[test]
fn pattern_annotation_protects_equals_only_for_an_active_owner() {
    for source in ["x: =T", "x: @ =T", "x: ="] {
        for stops in [0, PATTERN_STOP_EQUALS] {
            let (green, exit, completion, remainder) = run_required_pattern_with_context(
                source,
                stops,
                PatternMandatorySlotPolicy::default(),
                PatternCallerCloses::NONE,
                0,
                LineEntry::InLine,
                None,
            );
            assert_eq!(completion, PatternCompletion::Complete);
            if stops == 0 {
                assert_eq!(green.to_string(), source);
                assert_eq!(remainder, "");
                assert!(matches!(
                    exit,
                    NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
                ));
                assert_eq!(recovery_count(&green, SyntaxKind::Error), 1);
                assert_eq!(recovery_count(&green, SyntaxKind::Missing), 0);
            } else {
                let has_error = source.contains('@');
                assert_eq!(green.to_string(), if has_error { "x: @" } else { "x: " });
                assert_eq!(
                    recovery_count(&green, SyntaxKind::Error),
                    usize::from(has_error)
                );
                assert_eq!(
                    recovery_count(&green, SyntaxKind::Missing),
                    usize::from(!has_error)
                );
                assert_eq!(remainder, if source.ends_with('T') { "T" } else { "" });
                let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit
                else {
                    panic!("Pattern caller-owned Equals")
                };
                assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Equals));
                assert_eq!(
                    emit_pending_leading_text(&mut item),
                    if has_error { " " } else { "" }
                );
            }
        }
    }
}

#[test]
fn standalone_pattern_annotations_delegate_mandatory_type_recovery() {
    let (green, exit) = run_pattern("x: Int");
    assert_eq!(green.to_string(), "x: Int");
    assert!(matches!(exit, Err(Either::Right(_))));
    let annotation = annotation_node(&green);
    assert_eq!(
        annotation
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::TypeExpression]
    );
    assert!(!annotation.descendants_with_tokens().any(|node| matches!(
        node.kind(),
        SyntaxKind::Error | SyntaxKind::Invalid | SyntaxKind::Missing
    )));

    for (source, error, retry) in [
        ("x: @Int", "@", "Int"),
        ("x: @ Int", "@", " Int"),
        ("x: @\n  Int", "@", "\n  Int"),
        ("x: == Int", "==", " Int"),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let annotation = annotation_node(&green);
        assert_eq!(
            annotation
                .children_with_tokens()
                .filter(|element| element.as_node().is_some() || element.kind() == SyntaxKind::Error)
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [SyntaxKind::Error, SyntaxKind::TypeExpression],
            "{source:?}"
        );
        let error_node = crate::tests::recovery_output::recovery_groups(&annotation)
            .into_iter()
            .find(|group| group.parent().as_ref() == Some(&annotation))
            .expect("direct Type-primary Error");
        assert_eq!(error_node.text().to_string(), error, "{source:?}");
        let type_expr = annotation
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeExpression)
            .expect("retried TypeExpression");
        assert_eq!(type_expr.text().to_string(), retry, "{source:?}");
        assert!(
            !annotation
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    let (green, exit) = run_pattern("x: @");
    assert_eq!(green.to_string(), "x: @");
    assert!(matches!(exit, Err(Either::Right(_))));
    let annotation = annotation_node(&green);
    assert_eq!(
        annotation
            .children_with_tokens()
            .filter(|element| element.as_node().is_some() || element.kind() == SyntaxKind::Error)
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Error]
    );
    assert_eq!(
        annotation
            .children_with_tokens()
            .find(|element| element.kind() == SyntaxKind::Error)
            .expect("Type-primary Error")
            .to_string(),
        "@"
    );
    assert!(
        !annotation
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    let (green, exit) = run_pattern("x: @\nInt");
    assert_eq!(green.to_string(), "x: @");
    let Err(Either::Left(mut item)) = exit else {
        panic!("shallow newline handoff expected");
    };
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    assert_eq!(emit_pending_leading_text(&mut item), "\n");
    let annotation = annotation_node(&green);
    assert_eq!(
        annotation
            .children_with_tokens()
            .filter(|element| element.as_node().is_some() || element.kind() == SyntaxKind::Error)
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Error]
    );
    assert!(
        !annotation
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    for (source, expected_kind, expected_leading) in [
        ("x:", None, ""),
        ("x:,", Some(TokenKind::Comma), ""),
        ("x:;", Some(TokenKind::Semicolon), ""),
        ("x:)", Some(TokenKind::RParen), ""),
        ("x:]", Some(TokenKind::RBracket), ""),
        ("x:}", Some(TokenKind::RBrace), ""),
        ("x: =", Some(TokenKind::Equals), ""),
        ("x:\nInt", Some(TokenKind::Identifier), "\n"),
    ] {
        let (green, exit) = run_pattern(source);
        let mut item = match exit {
            Err(Either::Left(item)) => item,
            Err(Either::Right(end)) if expected_kind.is_none() => end.item,
            _ => panic!("mandatory Type boundary handoff expected: {source:?}"),
        };
        match expected_kind {
            Some(kind) => assert_eq!(item.payload_view().token_kind(), Some(kind), "{source:?}"),
            None => assert!(item.payload_view().is_eof(), "{source:?}"),
        }
        assert_eq!(
            emit_pending_leading_text(&mut item),
            expected_leading,
            "{source:?}"
        );
        let annotation = annotation_node(&green);
        assert_eq!(
            annotation
                .children()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [SyntaxKind::TypeExpression],
            "{source:?}"
        );
        assert_eq!(
            annotation
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !annotation
                .descendants_with_tokens()
                .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid)),
            "{source:?}"
        );
    }
}

#[test]
fn pattern_annotation_required_type_missing_has_direct_rowan_slot() {
    for (source, expected_leading) in [("x:", ""), ("x:\nInt", "\n")] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), "x:", "{source:?}");
        let mut item = if source == "x:" {
            let Err(Either::Right(end)) = exit else {
                panic!("EOF handoff expected");
            };
            assert!(end.item.payload_view().is_eof());
            end.item
        } else {
            let Err(Either::Left(item)) = exit else {
                panic!("shallow newline handoff expected");
            };
            assert_eq!(
                item.payload_view().token_kind(),
                Some(TokenKind::Identifier)
            );
            item
        };
        assert_eq!(emit_pending_leading_text(&mut item), expected_leading);

        let root = SyntaxNode::new_root(green);
        let pattern = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Pattern)
            .expect("Pattern");
        let annotation = pattern
            .children()
            .find(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
            .expect("direct PatternTypeAnnotation");
        assert_eq!(annotation.parent().as_ref(), Some(&pattern));
        assert_eq!(
            annotation.text_range(),
            rowan::TextRange::new(1.into(), 2.into())
        );
        let mut children = annotation.children_with_tokens();
        let colon = children
            .next()
            .expect("annotation Colon")
            .into_token()
            .expect("direct Colon token");
        assert_eq!(colon.kind(), SyntaxKind::Colon);
        assert_eq!(colon.parent().as_ref(), Some(&annotation));
        assert_eq!(
            colon.text_range(),
            rowan::TextRange::new(1.into(), 2.into())
        );
        let type_expr = children
            .next()
            .expect("required TypeExpression")
            .into_node()
            .expect("direct TypeExpression node");
        assert_eq!(type_expr.kind(), SyntaxKind::TypeExpression);
        assert_eq!(type_expr.parent().as_ref(), Some(&annotation));
        let missing_range = rowan::TextRange::empty(2.into());
        assert_eq!(type_expr.text_range(), missing_range);
        assert!(children.next().is_none());

        let mut type_children = type_expr.children_with_tokens();
        let missing = type_children
            .next()
            .expect("required Type Missing")
            .into_node()
            .expect("Missing node");
        assert_eq!(missing.kind(), SyntaxKind::Missing);
        assert_eq!(missing.parent().as_ref(), Some(&type_expr));
        assert_eq!(missing.text_range(), missing_range);
        assert!(missing.children_with_tokens().next().is_none());
        assert!(type_children.next().is_none());
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|element| element.kind() == SyntaxKind::Missing)
                .count(),
            1
        );
        assert!(
            !root
                .descendants_with_tokens()
                .any(|element| matches!(element.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
        );
    }
}

#[test]
fn pattern_annotation_required_type_primary_error_has_direct_rowan_slot() {
    for (source, consumed, error_end, retry_end) in [
        ("x: @", "x: @", 4, None),
        ("x: @ Int", "x: @ Int", 4, Some(8)),
        ("x: @ @ Int", "x: @ @ Int", 6, Some(10)),
        ("x: @\nInt", "x: @", 4, None),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), consumed, "{source:?}");
        if source == "x: @\nInt" {
            let Err(Either::Left(mut item)) = exit else {
                panic!("shallow newline handoff expected");
            };
            assert_eq!(
                item.payload_view().token_kind(),
                Some(TokenKind::Identifier)
            );
            assert_eq!(emit_pending_leading_text(&mut item), "\n");
        } else {
            assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        }

        let annotation = annotation_node(&green);
        assert_eq!(annotation.kind(), SyntaxKind::PatternTypeAnnotation);
        assert_eq!(
            annotation.text_range(),
            rowan::TextRange::new(1.into(), (consumed.len() as u32).into()),
            "{source:?}"
        );
        assert!(
            !annotation
                .descendants_with_tokens()
                .any(|element| matches!(element.kind(), SyntaxKind::Missing | SyntaxKind::Invalid))
        );
        let mut children = annotation.children_with_tokens().peekable();
        for (kind, start, end) in [(SyntaxKind::Colon, 1, 2), (SyntaxKind::Whitespace, 2, 3)] {
            let token = children
                .next()
                .expect("annotation punctuation or leading")
                .into_token()
                .expect("direct token");
            assert_eq!(token.kind(), kind, "{source:?}");
            assert_eq!(token.parent().as_ref(), Some(&annotation));
            assert_eq!(
                token.text_range(),
                rowan::TextRange::new(start.into(), end.into())
            );
        }

        let mut next_start = rowan::TextSize::from(3);
        while children
            .peek()
            .is_some_and(|element| element.kind() == SyntaxKind::Error)
        {
            let token = children.next().unwrap().into_token().expect("Error leaf");
            assert_eq!(token.parent().as_ref(), Some(&annotation));
            assert_eq!(token.text_range().start(), next_start, "{source:?}");
            assert!(!token.text_range().is_empty(), "{source:?}");
            next_start = token.text_range().end();
        }
        assert_eq!(next_start, rowan::TextSize::from(error_end), "{source:?}");

        if let Some(end) = retry_end {
            let retry = children
                .next()
                .expect("retry after maximal Error group")
                .into_node()
                .expect("direct TypeExpression node");
            assert_eq!(retry.kind(), SyntaxKind::TypeExpression);
            assert_eq!(retry.parent().as_ref(), Some(&annotation));
            assert_eq!(
                retry.text_range(),
                rowan::TextRange::new(error_end.into(), end.into())
            );
            let leading = retry
                .first_child_or_token()
                .expect("retry leading")
                .into_token()
                .expect("retry whitespace token");
            assert_eq!(leading.kind(), SyntaxKind::Whitespace);
            assert_eq!(leading.parent().as_ref(), Some(&retry));
            assert_eq!(
                leading.text_range(),
                rowan::TextRange::new(error_end.into(), (error_end + 1).into())
            );
        }
        assert!(children.next().is_none(), "{source:?}");
    }
}

#[test]
fn standalone_patterns_recover_primary_alias_and_alternation_slots_locally() {
    let (green, exit) = run_pattern("");
    assert!(matches!(exit, Err(Either::Right(_))));
    assert_eq!(
        pattern_node(green)
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run_pattern("@ x");
    assert_eq!(green.to_string(), "@ x");
    assert!(matches!(exit, Err(Either::Right(_))));
    let pattern = pattern_node(green);
    let errors = crate::tests::recovery_output::recovery_groups(&pattern)
        .into_iter()
        .filter(|group| group.parent().as_ref() == Some(&pattern))
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), "@");
    assert_eq!(
        errors[0].next_sibling_or_token().unwrap().kind(),
        SyntaxKind::Whitespace
    );
    assert!(
        pattern
            .children()
            .any(|node| node.kind() == SyntaxKind::IdentifierPattern)
    );
    assert_eq!(
        pattern
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        0
    );

    let (green, exit) = run_pattern("A as");
    assert_eq!(green.to_string(), "A as");
    assert!(matches!(exit, Err(Either::Right(_))));
    let alias = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::PatternAliasTail)
        .expect("PatternAliasTail");
    assert_eq!(
        alias
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run_pattern("A as $x");
    assert_eq!(green.to_string(), "A as $x");
    assert!(matches!(exit, Err(Either::Right(_))));
    let alias = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::PatternAliasTail)
        .expect("PatternAliasTail");
    let errors = crate::tests::recovery_output::recovery_groups(&alias)
        .into_iter()
        .filter(|group| group.parent().as_ref() == Some(&alias))
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), "$x");
    assert_eq!(
        alias
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        0
    );

    let (green, exit) = run_pattern("A |");
    assert_eq!(green.to_string(), "A |");
    assert!(matches!(exit, Err(Either::Right(_))));
    let alternation = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::PatternAlternationTail)
        .expect("PatternAlternationTail");
    assert_eq!(
        alternation
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run_pattern("A | | B");
    assert_eq!(green.to_string(), "A | | B");
    assert!(matches!(exit, Err(Either::Right(_))));
    let alternation = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::PatternAlternationTail)
        .expect("PatternAlternationTail");
    let rhs = alternation
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("alternation RHS");
    assert_eq!(
        rhs.children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert_eq!(
        rhs.children()
            .filter(|node| node.kind() == SyntaxKind::PatternAlternationTail)
            .count(),
        1
    );

    let (green, exit) = run_pattern(":");
    assert_eq!(green.to_string(), ":");
    assert!(matches!(exit, Err(Either::Right(_))));
    let symbol = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::SymbolPattern)
        .expect("SymbolPattern");
    assert_eq!(
        symbol
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    for (source, tail) in [
        ("@ as x", SyntaxKind::PatternAliasTail),
        ("@ : T", SyntaxKind::PatternTypeAnnotation),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let pattern = pattern_node(green);
        assert!(
            pattern.children().any(|node| node.kind() == tail),
            "{source:?}"
        );
    }

    let (green, exit) = run_pattern("A as @ ,");
    assert_eq!(green.to_string(), "A as @");
    let Err(Either::Left(mut item)) = exit else {
        panic!("comma handoff expected");
    };
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Comma));
    assert_eq!(emit_pending_leading_text(&mut item), " ");
    let alias = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::PatternAliasTail)
        .expect("PatternAliasTail");
    let errors = crate::tests::recovery_output::recovery_groups(&alias)
        .into_iter()
        .filter(|group| group.parent().as_ref() == Some(&alias))
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), "@");
    assert_eq!(
        alias
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        0
    );
}

#[test]
fn standalone_pattern_recovery_leaves_caller_boundaries_and_their_gaps_intact() {
    for (source, kind, leading) in [
        ("@ ,", TokenKind::Comma, " "),
        ("@ ]", TokenKind::RBracket, " "),
        ("@ : T", TokenKind::Colon, " "),
        ("@\nT", TokenKind::Identifier, "\n"),
    ] {
        let colon_stop = kind == TokenKind::Colon;
        let (green, exit) = run_pattern_with_colon_stop(source, colon_stop);
        assert_eq!(green.to_string(), "@", "{source:?}");
        let Err(Either::Left(mut item)) = exit else {
            panic!("caller boundary expected: {source:?}");
        };
        assert_eq!(item.payload_view().token_kind(), Some(kind), "{source:?}");
        assert_eq!(emit_pending_leading_text(&mut item), leading, "{source:?}");
    }
}

#[test]
fn standalone_patterns_keep_parenthesized_and_list_recovery_inside_their_owners() {
    for (source, owner, patterns, expected_missing, expected_errors) in [
        ("(,a)", SyntaxKind::ParenthesizedPattern, 2, 1, 0),
        ("(a b)", SyntaxKind::ParenthesizedPattern, 2, 1, 0),
        ("(a]", SyntaxKind::ParenthesizedPattern, 1, 1, 1),
        ("[,a]", SyntaxKind::ListPattern, 2, 1, 0),
        ("[a b]", SyntaxKind::ListPattern, 2, 1, 0),
        ("[..]", SyntaxKind::ListPattern, 1, 1, 0),
        ("[..,a]", SyntaxKind::ListPattern, 2, 1, 0),
        ("[..@tail]", SyntaxKind::ListPattern, 1, 0, 1),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let pattern = pattern_node(green);
        let delimited = pattern
            .children()
            .find(|node| node.kind() == owner)
            .expect("delimited Pattern owner");
        assert_eq!(
            delimited
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Pattern)
                .count(),
            patterns,
            "{source:?}"
        );
        assert_eq!(
            delimited
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected_missing,
            "{source:?}"
        );
        let errors = crate::tests::recovery_output::recovery_groups(&delimited)
            .into_iter()
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), expected_errors, "{source:?}");
        if source == "(a]" {
            assert_eq!(errors[0].text().to_string(), "]");
        }
        if source == "[..@tail]" {
            assert_eq!(errors[0].text().to_string(), "@");
        }
    }

    for (source, owner) in [
        ("(a\n", SyntaxKind::ParenthesizedPattern),
        ("[a\n", SyntaxKind::ListPattern),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        assert_eq!(trivia_parents(&green), [owner], "{source:?}");
    }
}

#[test]
fn standalone_patterns_keep_delimiter_and_malformed_list_item_recovery_local() {
    for (source, owner) in [
        ("(a", SyntaxKind::ParenthesizedPattern),
        ("[a", SyntaxKind::ListPattern),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let delimited = pattern_node(green)
            .children()
            .find(|node| node.kind() == owner)
            .expect("delimited Pattern owner");
        assert_eq!(
            delimited
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_pattern("[a, @ b]");
    assert_eq!(green.to_string(), "[a, @ b]");
    assert!(matches!(exit, Err(Either::Right(_))));
    let list = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::ListPattern)
        .expect("ListPattern");
    let items = list
        .children()
        .filter(|node| node.kind() == SyntaxKind::Pattern)
        .collect::<Vec<_>>();
    assert_eq!(items.len(), 2);
    let errors = crate::tests::recovery_output::recovery_groups(&items[1])
        .into_iter()
        .filter(|group| group.parent().as_ref() == Some(&items[1]))
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), "@");
    assert_eq!(
        errors[0].next_sibling_or_token().unwrap().kind(),
        SyntaxKind::Whitespace
    );
    assert!(
        items[1]
            .children()
            .any(|node| node.kind() == SyntaxKind::IdentifierPattern)
    );
    assert!(
        !items[1]
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    let (green, exit) = run_pattern("[...,a]");
    assert_eq!(green.to_string(), "[...,a]");
    assert!(matches!(exit, Err(Either::Right(_))));
    let list = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::ListPattern)
        .expect("ListPattern");
    let errors = crate::tests::recovery_output::recovery_groups(&list)
        .into_iter()
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), "...");
    assert!(
        !list
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ListPatternSpreadItem)
    );
    assert_eq!(
        list.children()
            .filter(|node| node.kind() == SyntaxKind::Pattern)
            .count(),
        2
    );
    assert_eq!(
        list.children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Comma)
            .count(),
        1
    );
}

#[test]
fn standalone_records_keep_recovery_slots_and_malformed_fixed_spellings_local() {
    let (green, exit) = run_pattern("{,a}");
    assert_eq!(green.to_string(), "{,a}");
    assert!(matches!(exit, Err(Either::Right(_))));
    let record = record_node(green);
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::RecordPatternField)
            .count(),
        1
    );

    let (green, exit) = run_pattern("{a; b}");
    assert_eq!(green.to_string(), "{a; b}");
    assert!(matches!(exit, Err(Either::Right(_))));
    let record = record_node(green);
    let errors = crate::tests::recovery_output::recovery_groups(&record)
        .into_iter()
        .filter(|group| group.parent().as_ref() == Some(&record))
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), ";");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::RecordPatternField)
            .count(),
        2
    );
    assert!(
        !record
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    let (green, exit) = run_pattern("{a:}");
    assert_eq!(green.to_string(), "{a:}");
    assert!(matches!(exit, Err(Either::Right(_))));
    let record = record_node(green);
    let field = record
        .children()
        .find(|node| node.kind() == SyntaxKind::RecordPatternField)
        .expect("RecordPatternField");
    let nested = field
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("nested Pattern");
    assert_eq!(
        nested
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run_pattern("{a =}");
    assert_eq!(green.to_string(), "{a =}");
    assert!(matches!(exit, Err(Either::Right(_))));
    let record = record_node(green);
    let field = record
        .children()
        .find(|node| node.kind() == SyntaxKind::RecordPatternField)
        .expect("RecordPatternField");
    assert!(
        field
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Equals)
    );
    let expression = field
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("mandatory default Expression product");
    assert_eq!(expression.to_string(), "");
    assert_eq!(expression.children().count(), 1);
    assert_eq!(
        expression.children().next().unwrap().kind(),
        SyntaxKind::Missing
    );

    let (green, exit) = run_pattern("{..}");
    assert_eq!(green.to_string(), "{..}");
    assert!(matches!(exit, Err(Either::Right(_))));
    let record = record_node(green);
    let spread = record
        .children()
        .find(|node| node.kind() == SyntaxKind::RecordPatternSpreadItem)
        .expect("RecordPatternSpreadItem");
    let nested = spread
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("spread Pattern");
    assert_eq!(
        nested
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run_pattern("{a b}");
    assert_eq!(green.to_string(), "{a b}");
    assert!(matches!(exit, Err(Either::Right(_))));
    let record = record_node(green);
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::RecordPatternField)
            .count(),
        2
    );
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run_pattern("{a");
    assert_eq!(green.to_string(), "{a");
    assert!(matches!(exit, Err(Either::Right(_))));
    assert_eq!(
        record_node(green)
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run_pattern("{a: @}");
    assert_eq!(green.to_string(), "{a: @}");
    assert!(matches!(exit, Err(Either::Right(_))));
    let field = record_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::RecordPatternField)
        .expect("RecordPatternField");
    let nested = field
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("nested Pattern");
    let errors = crate::tests::recovery_output::recovery_groups(&nested)
        .into_iter()
        .filter(|group| group.parent().as_ref() == Some(&nested))
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), "@");
    assert!(
        !nested
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    let (green, exit) = run_pattern("{a: = 1}");
    assert_eq!(green.to_string(), "{a: = 1}");
    assert!(matches!(exit, Err(Either::Right(_))));
    let field = record_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::RecordPatternField)
        .expect("RecordPatternField");
    let nested = field
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("nested Pattern");
    assert_eq!(
        nested
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        field
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Equals)
    );
    assert!(field.children().any(|node| {
        node.kind() == SyntaxKind::OperatorChain
            && node
                .descendants()
                .any(|node| node.kind() == SyntaxKind::IntegerLiteral)
    }));

    let (green, exit) = run_pattern("{a: @ p}");
    assert_eq!(green.to_string(), "{a: @ p}");
    assert!(matches!(exit, Err(Either::Right(_))));
    assert_eq!(
        trivia_parents(&green),
        [SyntaxKind::RecordPatternField, SyntaxKind::Pattern]
    );
    let field = record_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::RecordPatternField)
        .expect("RecordPatternField");
    let nested = field
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("nested Pattern");
    let errors = crate::tests::recovery_output::recovery_groups(&nested)
        .into_iter()
        .filter(|group| group.parent().as_ref() == Some(&nested))
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), "@");
    assert!(
        nested
            .children()
            .any(|node| node.kind() == SyntaxKind::IdentifierPattern)
    );
    assert!(
        !nested
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    let (green, exit) = run_pattern("{..@tail}");
    assert_eq!(green.to_string(), "{..@tail}");
    assert!(matches!(exit, Err(Either::Right(_))));
    let spread = record_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::RecordPatternSpreadItem)
        .expect("RecordPatternSpreadItem");
    let nested = spread
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("spread Pattern");
    let errors = crate::tests::recovery_output::recovery_groups(&nested)
        .into_iter()
        .filter(|group| group.parent().as_ref() == Some(&nested))
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), "@");
    assert!(
        nested
            .children()
            .any(|node| node.kind() == SyntaxKind::IdentifierPattern)
    );
    assert!(
        !nested
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    let (green, exit) = run_pattern("{...a}");
    assert_eq!(green.to_string(), "{...a}");
    assert!(matches!(exit, Err(Either::Right(_))));
    let record = record_node(green);
    let errors = crate::tests::recovery_output::recovery_groups(&record)
        .into_iter()
        .filter(|group| group.parent().as_ref() == Some(&record))
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), "...");
    assert!(
        !record
            .descendants()
            .any(|node| node.kind() == SyntaxKind::RecordPatternSpreadItem)
    );
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::RecordPatternField)
            .count(),
        1
    );

    for spelling in ["==", "=>", "=+"] {
        let source = format!("{{a {spelling} b}}");
        let (green, exit) = run_pattern(&source);
        assert_eq!(green.to_string(), source, "{spelling:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{spelling:?}");
        let record = record_node(green);
        let errors = crate::tests::recovery_output::recovery_groups(&record)
            .into_iter()
            .filter(|group| group.parent().as_ref() == Some(&record))
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{spelling:?}");
        assert_eq!(errors[0].text().to_string(), spelling);
        let leading = errors[0]
            .first_token()
            .unwrap()
            .prev_sibling_or_token()
            .unwrap();
        assert_eq!(leading.kind(), SyntaxKind::Whitespace);
        assert_eq!(leading.to_string(), " ");
        assert_eq!(
            errors[0].last_token().map(|token| token.kind()),
            Some(SyntaxKind::Error),
            "{spelling:?}"
        );
        assert!(
            !record
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Equals),
            "{spelling:?}"
        );
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::RecordPatternField)
                .count(),
            2,
            "{spelling:?}"
        );
        assert!(
            !record
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{spelling:?}"
        );
    }

    let (green, exit) = run_pattern(".");
    assert_eq!(green.to_string(), ".");
    assert!(matches!(exit, Err(Either::Right(_))));
    let error = crate::tests::recovery_output::recovery_groups(&pattern_node(green))
        .into_iter()
        .next()
        .expect("Pattern Error");
    assert_eq!(error.text().to_string(), ".");
    assert_eq!(
        error.first_token().map(|token| token.kind()),
        Some(SyntaxKind::Error)
    );
}

#[test]
fn standalone_patterns_keep_inter_child_trivia_with_the_introducing_owner() {
    let (green, exit) = run_pattern("A | B");
    assert!(matches!(exit, Err(Either::Right(_))));
    assert_eq!(
        trivia_parents(&green),
        [SyntaxKind::Pattern, SyntaxKind::PatternAlternationTail]
    );

    let (green, exit) = run_pattern("(A\nB)");
    assert!(matches!(exit, Err(Either::Right(_))));
    assert_eq!(trivia_parents(&green), [SyntaxKind::ParenthesizedPattern]);

    let (green, exit) = run_pattern("{a: b, c = 1}");
    assert!(matches!(exit, Err(Either::Right(_))));
    assert_eq!(
        trivia_parents(&green),
        [
            SyntaxKind::RecordPatternField,
            SyntaxKind::RecordPattern,
            SyntaxKind::RecordPatternField,
            SyntaxKind::RecordPatternField,
        ]
    );

    let (green, exit) = run_pattern("x : T");
    assert!(matches!(exit, Err(Either::Right(_))));
    assert_eq!(
        trivia_parents(&green),
        [SyntaxKind::Pattern, SyntaxKind::PatternTypeAnnotation]
    );

    for source in ["A |\n  B\n  : T", "A |\n  B\n    : T"] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let pattern = pattern_node(green);
        let alternation = pattern
            .children()
            .find(|node| node.kind() == SyntaxKind::PatternAlternationTail)
            .expect("PatternAlternationTail");
        let rhs = alternation
            .children()
            .find(|node| node.kind() == SyntaxKind::Pattern)
            .expect("alternation RHS");
        assert_eq!(
            rhs.children()
                .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
                .count(),
            0,
            "{source:?}"
        );
        assert_eq!(
            pattern
                .children()
                .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
                .count(),
            1,
            "{source:?}"
        );
    }

    for (source, annotations) in [("(A,\n  B\n  : T)", 0), ("(A,\n  B\n    : T)", 1)] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        assert_eq!(
            SyntaxNode::new_root(green)
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
                .count(),
            annotations,
            "{source:?}"
        );
    }
}

fn trivia_parents(green: &GreenNode) -> Vec<SyntaxKind> {
    SyntaxNode::new_root(green.clone())
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| matches!(token.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline))
        .map(|token| token.parent().expect("trivia parent").kind())
        .collect()
}

#[test]
fn pattern_literal_checkpoint_splits_one_quote_from_three_quote_string() {
    let (green, exit, remainder) = run_pattern_literal("\"a\\b:name\"tail");
    assert_eq!(remainder, "tail");
    assert_eq!(
        exit,
        PatternLiteralWitnessExit::Rule(RuleLiteralExit::Complete)
    );
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::RuleLiteral)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::StringLiteral)
            .count(),
        0
    );
    assert_eq!(
        root.first_token().map(|token| token.kind()),
        Some(SyntaxKind::RuleLiteralStart)
    );

    let (green, exit, remainder) = run_pattern_literal("\"\"\"α\"\"\"tail");
    assert_eq!(remainder, "tail");
    assert_eq!(
        exit,
        PatternLiteralWitnessExit::String(StringLiteralExit::Complete)
    );
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::StringLiteral)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::RuleLiteral)
            .count(),
        0
    );

    let (green, exit, remainder) = run_pattern_literal("\"\"\"a%{x}\"\"\"tail");
    assert_eq!(
        exit,
        PatternLiteralWitnessExit::String(StringLiteralExit::Complete)
    );
    assert_eq!(remainder, "tail");
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::StringInterpolation)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        1
    );
}

#[test]
fn l7_pattern_primary_routes_literals_without_an_expression_wrapper() {
    for (source, rules, strings) in [
        ("\"text:{capture}\"", 1, 0),
        ("\"text{value}\"", 1, 0),
        ("\"\"\"α\"\"\"", 0, 1),
        ("\"\"\"outer%{role R;}tail\"\"\"", 0, 1),
    ] {
        let (green, _, remainder) = run_l7_pattern(source);
        assert_eq!(remainder, "", "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(
            recovery_count(&green, SyntaxKind::RuleLiteral),
            rules,
            "{source:?}"
        );
        assert_eq!(
            recovery_count(&green, SyntaxKind::StringLiteral),
            strings,
            "{source:?}"
        );
        assert_eq!(recovery_count(&green, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(recovery_count(&green, SyntaxKind::Error), 0, "{source:?}");
        if source == "\"\"\"α\"\"\"" {
            assert_eq!(recovery_count(&green, SyntaxKind::OperatorChain), 0);
        }
    }

    let (green, _, remainder) = run_l7_pattern("\"\"tail");
    assert_eq!(remainder, "");
    assert_eq!(green.to_string(), "\"\"tail");
    assert_eq!(recovery_count(&green, SyntaxKind::RuleLiteral), 0);
    assert_eq!(recovery_count(&green, SyntaxKind::StringLiteral), 0);
    assert_eq!(recovery_count(&green, SyntaxKind::Error), 1);

    let operators = OperatorTable::empty();
    let recover = Recover::new_for_test(&operators);
    let mut input = "\"\"tail";
    let CurrentItem { item, .. } = current_item(
        chasa_recover::In::new(
            &mut input,
            &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
            (),
        ),
        0,
        LineEntry::InLine,
        None,
        |mut lex, leading, origin, fence, _| {
            scan_pattern_literal_payload(lex.rb())
                .or_else(|| scan_pattern_nud_payload(lex, leading, origin, fence, 0))
        },
    )
    .expect("two-quote Pattern Item");
    assert_eq!(item.payload_view().spelling(), Some("\"\""));
    assert_eq!(input, "tail");
}

#[test]
fn l7_pattern_literal_routes_preserve_multiline_and_fence_handoffs() {
    for (source, rule_literals, strings) in [
        ("\"a\nb\"", 1, 0),
        ("\"a\r\nb\"", 1, 0),
        ("\"\"\"a\nb\"\"\"", 0, 1),
        ("\"\"\"a\r\nb\"\"\"", 0, 1),
    ] {
        let (green, _, remainder) = run_l7_pattern(source);
        assert_eq!(remainder, "", "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(
            recovery_count(&green, SyntaxKind::RuleLiteral),
            rule_literals,
            "{source:?}"
        );
        assert_eq!(
            recovery_count(&green, SyntaxKind::StringLiteral),
            strings,
            "{source:?}"
        );
        assert_eq!(recovery_count(&green, SyntaxKind::Missing), 0, "{source:?}");
    }

    let boundary = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for source in ["> > \"a\n> stop\n", "> > \"\"\"a\n> stop\n"] {
        let (green, exit, remainder) =
            run_l7_pattern_with_context(source, 800, LineEntry::PhysicalStart, Some(&boundary));
        let NormalizedExit::Complete(Err(Either::Left(pending)), LineEntry::PhysicalStart) = exit
        else {
            panic!("Pattern literal must return the exact fence Item: {source:?}")
        };
        assert!(pending.payload_view().is_boundary(), "{source:?}");
        assert_eq!(remainder, "> stop\n", "{source:?}");
        assert_eq!(recovery_count(&green, SyntaxKind::Missing), 1, "{source:?}");
        assert_eq!(
            green.to_string(),
            source.strip_suffix("> stop\n").expect("fence suffix")
        );
    }
}

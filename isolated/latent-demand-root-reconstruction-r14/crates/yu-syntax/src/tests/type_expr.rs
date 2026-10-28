use crate::tests::recovery_output::recovery_groups;
use crate::tests::support::*;

use std::{ops::Range, sync::Arc};

use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
pub(super) use crate::structural_diagnostic::StructuralKind;
use chasa_recover::Recoverable as _;

// The bracket-row witnesses only need to distinguish an observed close token
// from an inserted missing close. Keep that test-local fact independent of
// the retired parser recovery vocabulary.
pub(super) enum Delimiter {
    Parenthesis,
}

mod arrow_rhs_cst;
mod bracket_arrow_cst;
mod bracket_arrow_recovery;
mod bracket_recovery;
mod equals_recovery;
mod forall_recovery;
mod leading_row_cst;
mod leading_row_recovery;
mod pe_recovery;
mod pv_recovery;
mod record_field_recovery;
mod record_sequence_recovery;
mod required_recovery;
mod type_call_fallback;
mod type_path_tail_cst;

fn top_type_expression(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeExpression)
        .expect("top-level type expression")
}

fn delimited_slot_children(
    node: &SyntaxNode,
) -> impl Iterator<Item = rowan::NodeOrToken<SyntaxNode, rowan::SyntaxToken<crate::YulangLanguage>>>
{
    node.children_with_tokens()
        .flat_map(|element| match element {
            rowan::NodeOrToken::Node(node) if node.kind() == SyntaxKind::TypeCallClose => {
                node.children_with_tokens().collect::<Vec<_>>()
            }
            element => vec![element],
        })
}

pub(super) type ExpectedStructural = StructuralFact;

fn run_pattern_with_structural_diagnostics(
    source: &str,
) -> (GreenNode, TailExit, Vec<StructuralFact>) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let mut exit = pattern_with_stops(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        PATTERN_DEFAULT_STOPS,
    );
    if let Err(Either::Right(end)) = &mut exit {
        emit_end(&mut output, end);
    }
    output.finish_node();
    let green = finish_with_discarded_recoveries(output, recover);
    let facts = structural_facts(&green);
    (green, exit, facts)
}

fn run_required_type_with_structural_diagnostics<'source>(
    source: &'source str,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (
    GreenNode,
    NormalizedExit,
    bool,
    &'source str,
    Vec<StructuralFact>,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let (primary, successor_origin, next_line_entry) = crate::type_expr::type_nud_item_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        item_origin,
        line_entry,
        fence,
    );
    let (mut exit, primary_found) =
        crate::type_expr::required_type_expr_with_caller_stops_and_completion_normalized(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
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
    let green = finish_with_discarded_recoveries(output, recover);
    let facts = structural_facts(&green);
    (green, exit, primary_found, input, facts)
}

fn assert_polymorphic_variant_deep_newline_boundary(
    source: &str,
    emitted: &str,
    leading: &str,
    local_error: Option<&str>,
) {
    let (green, exit, primary_found, remainder, facts) =
        run_required_type_with_structural_diagnostics(source, 0, LineEntry::InLine, None);
    assert!(primary_found, "{source:?}");
    assert_eq!(green.to_string(), emitted, "{source:?}");
    let NormalizedExit::Complete(Err(Either::Left(mut item)), _) = exit else {
        panic!("deep newline must leave its current Item pending: {source:?}")
    };
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    assert_eq!(item.payload_view().spelling(), Some("B"));
    assert_eq!(emit_pending_leading_text(&mut item), leading);
    assert_eq!(remainder, "}");

    let root = SyntaxNode::new_root(green);
    let variant = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    let local_errors = recovery_groups(&variant)
        .into_iter()
        .map(|node| node.text().to_string())
        .collect::<Vec<_>>();
    assert_eq!(
        local_errors,
        local_error
            .map(str::to_owned)
            .into_iter()
            .collect::<Vec<_>>(),
        "{source:?}"
    );
    assert_eq!(
        facts
            .iter()
            .filter(|(kind, _)| *kind == StructuralKind::ErrorGroup)
            .count(),
        usize::from(local_error.is_some()),
        "{source:?}"
    );
    assert_eq!(
        facts.len(),
        1 + usize::from(local_error.is_some()),
        "{source:?}"
    );
    assert_eq!(
        facts
            .iter()
            .filter(|(kind, _)| *kind == StructuralKind::Missing)
            .count(),
        1,
        "{source:?}"
    );
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1,
        "{source:?}"
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument),
        "{source:?}"
    );
}

fn run_type_with_context_and_structural_diagnostics(
    source: &str,
    type_ml: crate::type_expr::TypeMlContext,
) -> (GreenNode, NormalizedExit, Vec<StructuralFact>) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let (mut exit, _) = crate::type_expr::type_expr_with_context_for_test(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        type_ml,
        0,
    )
    .expect("accepted contextual TypeExpression");
    if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
        emit_end(&mut output, end);
    }
    output.finish_node();
    let green = finish_with_discarded_recoveries(output, recover);
    let facts = structural_facts(&green);
    (green, exit, facts)
}

struct ContextualTypeRun<'source> {
    green: GreenNode,
    exit: NormalizedExit,
    successor_origin: usize,
    remainder: &'source str,
    facts: Vec<StructuralFact>,
    mark: (),
    same_operators: bool,
}

#[allow(clippy::too_many_arguments)]
fn run_contextual_type_snapshot<'source>(
    source: &'source str,
    type_ml: crate::type_expr::TypeMlContext,
    caller_stops: Stops,
    outer_closes: u8,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> ContextualTypeRun<'source> {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mark = crate::cursor::LexRecover::new_for_test(recover.operators()).mark();
    let same_operators = std::ptr::eq(recover.operators(), &operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut output);
    let (mut exit, successor_origin) =
        crate::type_expr::type_expr_with_context_and_boundaries_for_test(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
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
    output.finish_node();
    let green = output.finish();
    let facts = structural_facts(&green);
    ContextualTypeRun {
        green,
        exit,
        successor_origin,
        remainder: input,
        facts,
        mark,
        same_operators,
    }
}

fn assert_complete_type_recovery(
    source: &str,
    origin: usize,
    expected: &[ExpectedStructural],
) -> SyntaxNode {
    let fresh = run_contextual_type_snapshot(
        source,
        crate::type_expr::TypeMlContext::INACTIVE,
        0,
        0,
        origin,
        LineEntry::InLine,
        None,
    );
    assert_eq!(fresh.green.to_string(), format!("sentinel{source}"));
    assert_eq!(fresh.successor_origin, origin + source.len(), "{source:?}");
    assert_eq!(fresh.remainder, "", "{source:?}");
    assert_eq!(fresh.mark, ());
    assert!(fresh.same_operators);
    let NormalizedExit::Complete(Err(Either::Right(_fresh_end)), fresh_line) = &fresh.exit else {
        panic!("complete Type must return EOF: {source:?}")
    };
    assert_eq!(*fresh_line, LineEntry::InLine);

    // Structural facts use red-tree byte ranges. The synthetic preceding
    // identifier is the only coordinate shift in this snapshot; `origin`
    // belongs to parser-item accounting and does not move the built tree.
    let expected = expected
        .iter()
        .map(|(kind, range)| {
            let start = range
                .start
                .checked_sub(origin)
                .expect("expected parser range must start at or after its item origin");
            let end = range
                .end
                .checked_sub(origin)
                .expect("expected parser range must end at or after its item origin");
            (*kind, "sentinel".len() + start.."sentinel".len() + end)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        structural_facts(&fresh.green),
        expected,
        "{source:?}, origin={origin}"
    );
    SyntaxNode::new_root(fresh.green)
}

pub(super) fn bracket_row_recovery_root(
    source: &str,
    expected: &[ExpectedStructural],
) -> SyntaxNode {
    assert_complete_type_recovery(source, 0, expected)
}

fn assert_parenthesized_t4p_topology(green: &GreenNode, expected: &[(SyntaxKind, Range<usize>)]) {
    let group = SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedTypeGroup)
        .expect("ParenthesizedTypeGroup");
    assert_direct_children_topology(&group, expected);
    assert!(
        !group
            .descendants_with_tokens()
            .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid)),
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

fn t4p_seeded_contexts() -> [(&'static str, crate::type_expr::TypeMlContext); 4] {
    [
        ("inactive", crate::type_expr::TypeMlContext::INACTIVE),
        (
            "outer-active",
            crate::type_expr::TypeMlContext::outer_active_for_test(),
        ),
        (
            "outer-dormant",
            crate::type_expr::TypeMlContext::outer_dormant_for_test(),
        ),
        (
            "non-TypeApply",
            crate::type_expr::TypeMlContext::non_type_apply_active_for_test(),
        ),
    ]
}

#[test]
fn type_parenthesized_context_matrix_preserves_phase_rejection_close_pending_and_fence() {
    for (label, context) in t4p_seeded_contexts() {
        let run = run_contextual_type_snapshot("(F A)", context, 0, 0, 0, LineEntry::InLine, None);
        assert_eq!(run.green.to_string(), "sentinel(F A)", "{label}");
        assert!(matches!(
            run.exit,
            NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
        ));
        assert_eq!(run.successor_origin, 5, "{label}");
        assert_eq!(run.remainder, "", "{label}");
        assert_eq!(run.mark, (), "{label}");
        assert!(run.same_operators, "{label}");
        let expects_separator = matches!(label, "outer-active" | "outer-dormant");
        assert_eq!(
            run.facts,
            if expects_separator {
                vec![(StructuralKind::Missing, 11..11)]
            } else {
                vec![]
            },
            "{label}"
        );
        assert_parenthesized_t4p_topology(
            &run.green,
            if expects_separator {
                &[
                    (SyntaxKind::LParen, 8..9),
                    (SyntaxKind::TypeExpression, 9..10),
                    (SyntaxKind::Whitespace, 10..11),
                    (SyntaxKind::Missing, 11..11),
                    (SyntaxKind::TypeExpression, 11..12),
                    (SyntaxKind::RParen, 12..13),
                ]
            } else {
                &[
                    (SyntaxKind::LParen, 8..9),
                    (SyntaxKind::TypeExpression, 9..12),
                    (SyntaxKind::RParen, 12..13),
                ]
            },
        );

        let eof = run_contextual_type_snapshot("(F", context, 0, 0, 0, LineEntry::InLine, None);
        assert_eq!(eof.facts, [(StructuralKind::Missing, 10..10)], "{label}");
        assert_eq!(eof.green.to_string(), "sentinel(F", "{label}");

        let pending = run_contextual_type_snapshot(
            "(F with tail",
            context,
            crate::lexical::stops::STOP_WITH,
            0,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(
            pending.facts,
            [(StructuralKind::Missing, 11..11)],
            "{label}"
        );
        let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = pending.exit
        else {
            panic!("caller boundary remains pending: {label}");
        };
        assert_eq!(item.payload_view().spelling(), Some("with"), "{label}");
        assert_eq!(pending.remainder, " tail", "{label}");
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
    for (label, context) in t4p_seeded_contexts() {
        let run = run_contextual_type_snapshot(
            "> > (F\n> > ```\nouter",
            context,
            0,
            0,
            0,
            LineEntry::PhysicalStart,
            Some(&fence),
        );
        let [fact] = run.facts.as_slice() else {
            panic!("one close fact: {label}")
        };
        assert_eq!(fact.0, StructuralKind::Missing, "{label}");
        let group = parenthesized_group(&run.green);
        assert_eq!(
            fact.1,
            usize::from(group.text_range().end())..usize::from(group.text_range().end())
        );
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) =
            run.exit
        else {
            panic!("fence boundary remains pending: {label}");
        };
        assert!(boundary.payload_view().is_boundary(), "{label}");
        assert_eq!(run.remainder, "> > ```\nouter", "{label}");
    }

    let operators = OperatorTable::empty();
    for (label, context) in t4p_seeded_contexts() {
        let mut input = "@";
        let mut recover = Recover::new_for_test(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        seed_identifier(&mut output);
        assert!(
            crate::type_expr::type_expr_with_context_for_test(
                crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                context,
                0,
            )
            .is_none(),
            "{label}"
        );
        assert_eq!(input, "@", "{label}");
        output.finish_node();
        let green = finish_with_discarded_recoveries(output, recover);
        assert_eq!(green.to_string(), "sentinel", "{label}");
    }
}

fn run_required_type_with_outer_boundary_and_structural_diagnostics<'source>(
    source: &'source str,
    outer_boundary: crate::type_expr::TypeOuterBoundary,
    pipe_lexical: bool,
) -> (
    GreenNode,
    NormalizedExit,
    bool,
    usize,
    &'source str,
    Vec<StructuralFact>,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let (primary, primary_successor, line_entry) = crate::type_expr::type_nud_item_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        0,
        LineEntry::InLine,
        None,
    );
    let continuation_entry = crate::lexical::position::suffix_marker(crate::cursor::SyntaxIn::new(
        &mut input,
        &mut recover,
        &mut output,
    ));
    let (exit, primary_found) = if pipe_lexical {
        crate::type_expr::required_variant_payload_type_normalized(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            primary,
            0,
            crate::type_expr::TypeMlContext::INACTIVE,
            outer_boundary,
            primary_successor,
            line_entry,
            None,
        )
    } else {
        crate::type_expr::required_type_expr_with_caller_stops_and_outer_boundary_normalized(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            primary,
            0,
            0,
            outer_boundary,
            primary_successor,
            line_entry,
            None,
        )
    };
    let successor_origin = crate::lexical::position::advanced_origin(
        primary_successor,
        continuation_entry,
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
    );
    output.finish_node();
    let green = finish_with_discarded_recoveries(output, recover);
    let diagnostics = structural_facts(&green);
    (
        green,
        exit,
        primary_found,
        successor_origin,
        input,
        diagnostics,
    )
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
    let recover = Recover::new_for_test(operators);
    let mark = crate::cursor::LexRecover::new_for_test(recover.operators()).mark();
    let same_operators = std::ptr::eq(recover.operators(), operators);
    let crate::lexical::current_item::CurrentItem {
        item,
        next_line_entry,
    } = crate::lexical::current_item::current_item(
        chasa_recover::In::new(
            &mut input,
            &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
            (),
        ),
        item_origin,
        LineEntry::InLine,
        None,
        |mut lex, leading, origin, fence, _| {
            if pipe_lexical && let Some(pipe) = lex.token(crate::lexical::lexer::scan_exact_pipe) {
                return Some(crate::lexical::current_item::AcceptedPayload {
                    payload: crate::lexical::current_item::CurrentPayload::Token(pipe),
                    next_line_entry: LineEntry::InLine,
                });
            }
            crate::lexical::lexer::scan_type_nud_payload(lex, leading, origin, fence)
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
    let mut expected = vec![(StructuralKind::Invalid, 2..close_at)];
    if let Some(range) = item_error {
        expected.push(pe_recovery::item(1, false, range, true));
    }
    expected.push((StructuralKind::Missing, (close_at)..(close_at)));
    let (green, exit, facts) = run_type_with_structural_diagnostics(source);
    assert_eq!(green.to_string(), source, "{source:?}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
    assert_eq!(facts, expected, "{source:?}");
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
    expected.push((StructuralKind::ErrorGroup, at..at + 1));
    expected.push((StructuralKind::Missing, (source.len())..(source.len())));
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
    let foreign_close = group
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeDelimitedForeignClose)
        .expect("protected foreign close");
    assert_eq!(foreign_close.text(), "]");
    assert_eq!(
        foreign_close
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Error]
    );
}

#[test]
fn required_type_primary_preserves_boundaries_and_accepts_an_ordinary_primary() {
    for (source, kind) in [
        (",A", TokenKind::Comma),
        (";A", TokenKind::Semicolon),
        (")A", TokenKind::RParen),
        ("]A", TokenKind::RBracket),
        ("}A", TokenKind::RBrace),
    ] {
        let (green, exit, primary_found, remainder, facts) =
            run_required_type_with_structural_diagnostics(source, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "", "{source:?}");
        let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
            panic!("required Type boundary must remain pending: {source:?}")
        };
        assert_eq!(item.payload_view().token_kind(), Some(kind), "{source:?}");
        assert_eq!(remainder, "A", "{source:?}");
        assert!(!primary_found, "{source:?}");
        assert_eq!(facts, [(StructuralKind::Missing, (0)..(0))], "{source:?}");
        let type_expr = SyntaxNode::new_root(green)
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeExpression)
            .expect("typed missing required TypeExpression");
        assert_eq!(
            type_expr
                .children()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [SyntaxKind::Missing],
            "{source:?}"
        );
    }

    let (green, exit, primary_found, remainder, facts) =
        run_required_type_with_structural_diagnostics("A", 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "A");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
    ));
    assert!(primary_found);
    assert_eq!(remainder, "");
    assert!(facts.is_empty());

    let (green, exit, primary_found, remainder, facts) =
        run_required_type_with_structural_diagnostics("", 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
    ));
    assert!(!primary_found);
    assert_eq!(remainder, "");
    assert_eq!(facts, [(StructuralKind::Missing, (0)..(0))]);
    assert_eq!(
        SyntaxNode::new_root(green)
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeExpression)
            .expect("typed EOF missing TypeExpression")
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
    let (green, exit, primary_found, remainder, facts) =
        run_required_type_with_structural_diagnostics(
            source,
            0,
            LineEntry::PhysicalStart,
            Some(&fence),
        );
    assert_eq!(green.to_string(), "");
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart) = exit else {
        panic!("required Type must preserve the fence boundary")
    };
    assert!(item.payload_view().is_boundary());
    assert!(item.leading_view().has_ordinary_newline());
    assert!(!primary_found);
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(facts, [(StructuralKind::Missing, (0)..(0))]);
    assert_eq!(
        SyntaxNode::new_root(green)
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeExpression)
            .expect("typed fence missing TypeExpression")
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Missing]
    );
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
        delimited_slot_children(&call)
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
            .descendants_with_tokens()
            .any(|node| matches!(
                node.kind(),
                SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
            ))
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
            path.children_with_tokens()
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
fn type_contextual_names_belong_to_paths_and_nested_calls() {
    use crate::type_expr::TypeOuterBoundary;

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
                let (green, exit, accepted, origin, remainder, facts) =
                    run_required_type_with_outer_boundary_and_structural_diagnostics(
                        &source, boundary, false,
                    );
                assert!(accepted, "{source:?}");
                assert_eq!(green.to_string(), body, "{source:?}");
                assert_eq!(origin, source.len(), "{source:?}");
                assert_eq!(remainder, "", "{source:?}");
                assert!(facts.is_empty(), "{source:?}: {facts:?}");
                if suffix.is_empty() {
                    assert!(
                        matches!(
                            exit,
                            NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
                        ),
                        "{source:?}"
                    );
                } else {
                    let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) =
                        exit
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
                    !root.descendants_with_tokens().any(|node| {
                        matches!(
                            node.kind(),
                            SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
                        )
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
            }
        }
    }
}

#[test]
fn type_path_segment_valid_controls_publish_no_recovery() {
    for source in ["A::B", "A:: B", "A::'b"] {
        let (green, exit, facts) = run_type_with_structural_diagnostics(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(facts.is_empty(), "{source:?}");
        assert!(
            !SyntaxNode::new_root(green)
                .descendants_with_tokens()
                .any(|node| matches!(
                    node.kind(),
                    SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
                ))
        );
    }
}

#[test]
fn type_path_segment_shifted_origin_preserves_local_cst_ranges() {
    for (source, local, global) in [
        ("A::@", 3..4, 18..19),
        ("A::@@B", 3..5, 18..20),
        ("A::@/*x*/ B", 3..9, 18..24),
    ] {
        let (green, exit, primary_found, remainder, facts) =
            run_required_type_with_structural_diagnostics(source, 15, LineEntry::InLine, None);
        assert!(primary_found, "{source:?}");
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
        assert_eq!(remainder, "", "{source:?}");
        assert_eq!(facts, [(StructuralKind::ErrorGroup, local.clone())]);
        let error = recovery_groups(&SyntaxNode::new_root(green))
            .into_iter()
            .next()
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
            crate::type_expr::TypeOuterBoundary::WITH,
            false,
            TokenKind::Identifier,
            " ",
        ),
        (
            "A::@/*x*/ with",
            crate::type_expr::TypeOuterBoundary::WITH,
            false,
            TokenKind::Identifier,
            "/*x*/ ",
        ),
        (
            "A::@ = Body",
            crate::type_expr::TypeOuterBoundary::EQUALS,
            false,
            TokenKind::Equals,
            " ",
        ),
        (
            "A::@ | Body",
            crate::type_expr::TypeOuterBoundary::PIPE,
            true,
            TokenKind::Pipe,
            " ",
        ),
        (
            "A::@ : Body",
            crate::type_expr::TypeOuterBoundary::STRUCT_BODY,
            false,
            TokenKind::Colon,
            " ",
        ),
        (
            "A::@ ; Body",
            crate::type_expr::TypeOuterBoundary::VARIANT_BODY,
            false,
            TokenKind::Semicolon,
            " ",
        ),
    ] {
        let (green, exit, primary_found, _, _, facts) =
            run_required_type_with_outer_boundary_and_structural_diagnostics(
                source,
                outer_boundary,
                pipe_lexical,
            );
        let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) = exit
        else {
            panic!("outer boundary remains pending: {source:?}")
        };
        assert!(primary_found, "{source:?}");
        assert_eq!(green.to_string(), "A::@", "{source:?}");
        assert_eq!(facts, [(StructuralKind::ErrorGroup, 3..4)], "{source:?}",);
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
    }

    let operators = OperatorTable::empty();
    for (source, leading_text) in [("A::@ )", " "), ("A::@/*x*/ )", "/*x*/ ")] {
        let mut input = source;
        let mut recover = Recover::new_for_test(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (exit, _) = crate::type_expr::type_expr_with_caller_stops_for_test(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            crate::lexical::stops::stops_for(TokenKind::RParen),
            0,
            0,
        )
        .expect("accepted PathSegment Type");
        let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) = exit
        else {
            panic!("close remains pending: {source:?}")
        };
        output.finish_node();
        let green = finish_with_discarded_recoveries(output, recover);
        let facts = structural_facts(&green);
        assert_eq!(green.to_string(), "A::@", "{source:?}");
        assert_eq!(facts, [(StructuralKind::ErrorGroup, 3..4)]);
        assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::RParen));
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            leading_text,
            "{source:?}"
        );
    }

    for source in ["A::@\nB", "A::@\r\nB", "A::@ \nB", "A::@ \r\nB"] {
        let (green, exit, facts) = run_type_with_structural_diagnostics(source);
        assert_eq!(green.to_string(), "A::@", "{source:?}");
        assert_eq!(facts, [(StructuralKind::ErrorGroup, 3..4)]);
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

    let (green, _, facts) = run_type_with_structural_diagnostics("A::::B");
    assert_eq!(green.to_string(), "A::::B");
    assert_eq!(facts, [(StructuralKind::Missing, 3..3)]);
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
                .children_with_tokens()
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
fn type_arrow_rhs_error_keeps_shallow_newline_item_and_accepts_deeper_retry() {
    let operators = OperatorTable::empty();
    for newline in ["\n", "\r\n"] {
        for indentation in ["", "  ", "    "] {
            let source = format!("A ->@{newline}{indentation}B");
            let mut input = source.as_str();
            let mut recover = Recover::new_for_test(&operators);
            let mut output = GreenNodeBuilder::new();
            output.start_node(SyntaxKind::Root.into());
            let (primary, origin, line) = crate::type_expr::type_nud_item_normalized(
                crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                0,
                LineEntry::InLine,
                None,
            );
            let (exit, accepted) =
                crate::type_expr::required_type_expr_with_caller_stops_and_outer_boundary_normalized(
                    crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                    primary,
                    2,
                    0,
                    crate::type_expr::TypeOuterBoundary::NONE,
                    origin,
                    line,
                    None,
                );
            assert!(accepted);
            let successor_origin = source.len() - input.len();
            output.finish_node();
            let green = finish_with_discarded_recoveries(output, recover);
            let root = SyntaxNode::new_root(green);
            let arrow = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
                .expect("TypeArrowTail");
            assert!(
                !root
                    .descendants()
                    .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Invalid))
            );
            if indentation.len() <= 2 {
                assert_eq!(root.to_string(), "A ->@", "{source:?}");
                assert_eq!(
                    arrow
                        .children_with_tokens()
                        .map(|element| (element.kind(), element.to_string()))
                        .collect::<Vec<_>>(),
                    [
                        (SyntaxKind::Whitespace, " ".to_owned()),
                        (SyntaxKind::Arrow, "->".to_owned()),
                        (SyntaxKind::Error, "@".to_owned()),
                    ],
                    "{source:?}"
                );
                let NormalizedExit::Complete(Err(Either::Left(item)), line) = exit else {
                    panic!("shallow newline and its identifier must remain pending: {source:?}")
                };
                let (control, origin, control_line, remainder, _, _) =
                    scan_type_item_control(&source[5..], 5, &operators);
                assert_eq!(item, control, "{source:?}");
                assert_eq!(
                    item.extent(successor_origin).recovery_range(),
                    5..source.len()
                );
                assert_eq!(successor_origin, origin);
                assert_eq!(line, control_line);
                assert_eq!(input, remainder);
            } else {
                assert_eq!(root.to_string(), source);
                assert!(matches!(
                    exit,
                    NormalizedExit::Complete(Err(Either::Right(_)), _)
                ));
                let rhs = arrow
                    .children()
                    .find(|node| node.kind() == SyntaxKind::TypeExpression)
                    .expect("deeper retry remains the Arrow RHS");
                assert!(rhs.descendants_with_tokens().any(|element| {
                    element.kind() == SyntaxKind::Identifier && element.to_string() == "B"
                }));
                assert_eq!(input, "");
            }
        }
    }
}

#[test]
fn type_arrow_rhs_valid_control_has_no_recovery() {
    let source = "A -> B";
    let (green, exit, facts) = run_type_with_structural_diagnostics(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(facts.is_empty());
    assert!(
        !SyntaxNode::new_root(green)
            .descendants_with_tokens()
            .any(|node| matches!(
                node.kind(),
                SyntaxKind::Error | SyntaxKind::Invalid | SyntaxKind::Missing
            ))
    );
}

#[test]
fn type_parenthesized_t4p_nested_typeapply_restores_non_typeapply_payload_phase() {
    let source = ":{Tag (G (F A)) (F A)}";
    let (green, exit, facts) = run_type_with_structural_diagnostics(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(facts, [(StructuralKind::Missing, (12)..(12))]);
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
    let restored = groups[1]
        .children()
        .find(|node| node.kind() == SyntaxKind::Missing)
        .expect("the nested TypeApply separator belongs to its inner group");
    assert_eq!(usize::from(restored.text_range().start()), 12);
    assert_eq!(restored.parent(), Some(groups[1].clone()));
    assert_eq!(groups[1].text().to_string(), "(F A)");
    assert!(
        groups[2]
            .children()
            .all(|node| node.kind() != SyntaxKind::Missing),
        "the following non-TypeApply payload must see restored context"
    );
}

#[test]
fn type_call_t3b_publishes_argument_error_and_maps_missing_source_range() {
    let (green, exit, facts) = run_type_with_structural_diagnostics("T(@A)");
    assert_eq!(green.to_string(), "T(@A)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(facts, [(StructuralKind::ErrorGroup, 2..3)]);
    let error = recovery_groups(&SyntaxNode::new_root(green))
        .into_iter()
        .next()
        .expect("typed CallArgument Error");
    assert_eq!(error.text(), "@");
    assert_eq!(
        error
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [(SyntaxKind::Error, "@".to_owned())],
    );

    let expected = vec![
        (StructuralKind::Missing, (2)..(2)),
        (StructuralKind::Missing, (2)..(2)),
    ];
    let (green, exit, remainder, facts) =
        run_type_normalized_with_structural_diagnostics("T(", 13, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "T(");
    assert!(matches!(
        exit,
        Some(NormalizedExit::Complete(
            Err(Either::Right(_)),
            LineEntry::InLine
        ))
    ));
    assert_eq!(remainder, "");
    assert_eq!(facts, expected);
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
fn type_call_t3b_argument_error_preserves_local_cst_range() {
    let source = "T(@ A)";
    let (green, exit, remainder, facts) =
        run_type_normalized_with_structural_diagnostics(source, 13, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    assert!(matches!(
        exit,
        Some(NormalizedExit::Complete(
            Err(Either::Right(_)),
            LineEntry::InLine
        ))
    ));
    assert_eq!(facts, [(StructuralKind::ErrorGroup, 2..4)]);
    let error = recovery_groups(&SyntaxNode::new_root(green))
        .into_iter()
        .next()
        .expect("CallArgument Error");
    assert_eq!(
        usize::from(error.text_range().start())..usize::from(error.text_range().end()),
        2..4,
    );
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
            delimited_slot_children(&owner)
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
            recovery_groups(&owner)
                .into_iter()
                .filter(|group| group.parent().as_ref() == Some(&owner))
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
        delimited_slot_children(&call)
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count()
            + recovery_groups(&call).len(),
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
        ]
    );
    let close = record.last_child().expect("named record close");
    assert_eq!(close.kind(), SyntaxKind::NamedRecordTypeClose);
    assert_eq!(
        close
            .children_with_tokens()
            .map(|element| (element.kind(), element.to_string()))
            .collect::<Vec<_>>(),
        [(SyntaxKind::RBrace, "}".to_owned())]
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
    assert_eq!(green.to_string(), "{a: A,]");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
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
    assert_eq!(green.to_string(), "{a: A]");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
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
        let error = recovery_groups(&record)
            .into_iter()
            .find(|group| group.parent().as_ref() == Some(&record))
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
        recovery_groups(&record)
            .into_iter()
            .find(|group| group.parent().as_ref() == Some(&record))
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
            recovery_groups(&field)
                .into_iter()
                .filter(|group| group.parent().as_ref() == Some(&field))
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            recovery_groups(&field)
                .into_iter()
                .find(|group| group.parent().as_ref() == Some(&field))
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
        let separator = record
            .children()
            .find(|node| node.kind() == SyntaxKind::NamedRecordTypeSeparator)
            .expect("separator slot");
        let error = recovery_groups(&separator)
            .into_iter()
            .find(|group| group.parent().as_ref() == Some(&separator))
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
    let separator = record
        .children()
        .find(|node| node.kind() == SyntaxKind::NamedRecordTypeSeparator)
        .expect("separator slot");
    assert_eq!(
        recovery_groups(&separator)
            .into_iter()
            .find(|group| group.parent().as_ref() == Some(&separator))
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
            recovery_groups(&field)
                .into_iter()
                .filter(|group| group.parent().as_ref() == Some(&field))
                .count(),
            1,
            "{source:?}"
        );
        let error = recovery_groups(&field)
            .into_iter()
            .find(|group| group.parent().as_ref() == Some(&field))
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
        let error = recovery_groups(&field)
            .into_iter()
            .find(|group| group.parent().as_ref() == Some(&field))
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
        let errors = recovery_groups(&forall).into_iter().collect::<Vec<_>>();
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
    for (source, malformed) in [("for, T", ", T"), ("for; T", "; T")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        let error = recovery_groups(&forall)
            .into_iter()
            .next()
            .expect("malformed first binder");
        assert_eq!(error.text().to_string(), malformed, "{source:?}");
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
        let error = recovery_groups(&forall)
            .into_iter()
            .next()
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
                .descendants_with_tokens()
                .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid)),
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
            recovery_groups(&forall)
                .into_iter()
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
                .descendants_with_tokens()
                .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid)),
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
                .descendants_with_tokens()
                .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid)),
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
            recovery_groups(&record)
                .into_iter()
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            record_error.into_iter().collect::<Vec<_>>(),
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(
                    |token| matches!(token.kind(), SyntaxKind::Comma | SyntaxKind::Semicolon)
                        || (token.kind() == SyntaxKind::Error && token.text() == separator)
                )
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
            .descendants_with_tokens()
            .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
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
        ("for 'a @ 'b: T", "@", 0, 2),
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
            recovery_groups(&forall)
                .into_iter()
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
            .descendants_with_tokens()
            .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
    );

    let malformed_colon = run_type("for 'a @: T").0;
    let malformed_colon = SyntaxNode::new_root(malformed_colon)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type");
    assert!(
        malformed_colon
            .children_with_tokens()
            .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
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
        2
    );

    let nested = run_type("for (@: T) 'a: T").0;
    let nested = SyntaxNode::new_root(nested);
    assert_eq!(
        recovery_groups(&nested)
            .into_iter()
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["(@: T)"]
    );

    let nested_newline = run_type("for (@\n) 'a: T").0;
    let nested_newline = SyntaxNode::new_root(nested_newline);
    assert_eq!(
        recovery_groups(&nested_newline)
            .into_iter()
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
                let mut expected = vec![(StructuralKind::Invalid, origin + 2..at)];
                if missing_count == 2 {
                    expected.push((StructuralKind::Missing, (at)..(at)));
                }
                if missing_count > 0 {
                    match owner {
                        SyntaxKind::TypeCallTail => {
                            expected.push((StructuralKind::Missing, (at)..(at)))
                        }
                        SyntaxKind::ParenthesizedTypeGroup => {
                            expected.push((StructuralKind::Missing, (at)..(at)));
                        }
                        SyntaxKind::EffectRowType => {
                            expected.push(pe_recovery::close(
                                expected.len() as u32,
                                true,
                                at..at,
                                false,
                            ));
                        }
                        _ => unreachable!(),
                    }
                }
                for suffix in ["", "::Next"] {
                    let source = format!("{base}{suffix}");
                    let root = assert_complete_type_recovery(&source, origin, &expected);
                    let errors = recovery_groups(&root).into_iter().collect::<Vec<_>>();
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
                    let gaps = delimited_slot_children(&delimited)
                        .filter(|child| child.kind() == SyntaxKind::Whitespace)
                        .collect::<Vec<_>>();
                    assert_eq!(gaps.len(), usize::from(gap_start.is_some()));
                    if let Some(start) = gap_start {
                        assert_eq!(gaps[0].to_string(), " ");
                        assert_eq!(usize::from(gaps[0].text_range().start()), 8 + start);
                        assert_eq!(usize::from(gaps[0].text_range().end()), 8 + start + 1);
                    }
                    let missing = delimited_slot_children(&delimited)
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
                        assert!(delimited_slot_children(&delimited).any(|child| {
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
                (StructuralKind::ErrorGroup, 2..3),
                (StructuralKind::Invalid, 4..7),
                (StructuralKind::Missing, (7)..(7)),
            ],
        ),
        (
            ":{@ '[F }",
            vec![
                (StructuralKind::ErrorGroup, 2..3),
                (StructuralKind::Invalid, 4..8),
                pe_recovery::close(2, true, 8..8, false),
            ],
        ),
        (
            ":{:{(A }}",
            vec![
                (StructuralKind::Invalid, 2..8),
                (StructuralKind::Invalid, 4..7),
                (StructuralKind::Missing, (7)..(7)),
            ],
        ),
        (
            ":{:{'[F }}",
            vec![
                (StructuralKind::Invalid, 2..9),
                (StructuralKind::Invalid, 4..8),
                pe_recovery::close(2, true, 8..8, false),
            ],
        ),
    ] {
        for suffix in ["", "::Next"] {
            let source = format!("{base}{suffix}");
            let root = assert_complete_type_recovery(&source, 0, &expected);
            let errors = recovery_groups(&root).into_iter().collect::<Vec<_>>();
            let error_facts = expected
                .iter()
                .filter(|(kind, _)| {
                    matches!(kind, StructuralKind::ErrorGroup | StructuralKind::Invalid)
                })
                .collect::<Vec<_>>();
            assert_eq!(errors.len(), error_facts.len());
            for (node, (_, range)) in errors.iter().zip(error_facts) {
                assert_eq!(usize::from(node.text_range().start()), 8 + range.start);
                assert_eq!(usize::from(node.text_range().end()), 8 + range.end);
                assert_eq!(node.text().to_string(), &base[range.clone()]);
            }
            assert_eq!(
                errors[0]
                    .descendants()
                    .any(|node| errors[1].parent().as_ref() == Some(&node)),
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
            !root.descendants_with_tokens().any(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::Error | SyntaxKind::Invalid | SyntaxKind::Missing
                )
            }),
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
fn polymorphic_variant_structured_tag_name_orders_structural_recovery() {
    let source = ":{@ (A}";
    let (green, exit, facts) = run_type_with_structural_diagnostics(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        facts,
        [
            (StructuralKind::ErrorGroup, 2..3),
            (StructuralKind::Invalid, 4..6),
            (StructuralKind::Missing, (6)..(6)),
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
    assert_eq!(tag_children[2].kind(), SyntaxKind::Invalid);
    let structured = tag_children[2]
        .clone()
        .into_node()
        .expect("structured tag-name Invalid");
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
}

#[test]
fn polymorphic_variant_recursive_structured_tag_names_are_lifo_and_reusable() {
    let source = ":{:{123}}";
    let (green, exit, facts) = run_type_with_structural_diagnostics(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        facts,
        [
            (StructuralKind::Invalid, 2..8),
            (StructuralKind::Invalid, 4..7),
        ]
    );
    let root = SyntaxNode::new_root(green.clone());
    let structured = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Invalid)
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
}

#[test]
fn polymorphic_variant_structured_tag_name_single_and_valid_controls() {
    let (green, exit, facts) = run_type_with_structural_diagnostics(":{123}");
    assert_eq!(green.to_string(), ":{123}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(facts, [(StructuralKind::Invalid, 2..5)]);

    let (green, exit, facts) = run_type_with_structural_diagnostics(":{A}");
    assert_eq!(green.to_string(), ":{A}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(facts.is_empty());
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
    let (green, exit, facts) = run_type_with_structural_diagnostics("(A)");
    assert_eq!(green.to_string(), "(A)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(facts.is_empty());
}

#[test]
fn parenthesized_close_eof() {
    let (green, exit, facts) = run_type_with_structural_diagnostics("(A");
    assert_eq!(green.to_string(), "(A");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(facts, [(StructuralKind::Missing, (2)..(2))]);
}

#[test]
fn parenthesized_close_trivia_prefixed_outer_anchor() {
    let source = ":{(A }";
    let (green, exit, facts) = run_type_with_structural_diagnostics(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        facts,
        [
            (StructuralKind::Invalid, 2..5),
            (StructuralKind::Missing, (5)..(5)),
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
    let (green, exit, remainder, facts) = run_type_normalized_with_structural_diagnostics(
        source,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
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
    assert_eq!(facts, [(StructuralKind::Missing, (6)..(6))]);
}

#[test]
fn parenthesized_close_nonclose_caller_boundary() {
    let operators = OperatorTable::empty();
    let mut input = "(A with";
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let (exit, successor_origin) = crate::type_expr::type_expr_with_caller_stops_for_test(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        crate::lexical::stops::STOP_WITH,
        0,
        0,
    )
    .expect("accepted parenthesized Type");
    output.finish_node();
    let green = finish_with_discarded_recoveries(output, recover);
    let facts = structural_facts(&green);
    assert_eq!(green.to_string(), "(A ");
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
        panic!("active non-close caller boundary must remain pending")
    };
    assert_eq!(item.payload_view().spelling(), Some("with"));
    assert_eq!(item.leading_view().remaining_physical_parts(), 0);
    assert_eq!(input, "");
    assert_eq!(successor_origin, 7);
    assert_eq!(facts, [(StructuralKind::Missing, (3)..(3))]);
}

#[test]
fn type_delimited_owner_routing_publishes_effect_and_bracket_close_records() {
    for (source, expected) in [
        ("'[A", vec![pe_recovery::close(0, true, 3..3, false)]),
        (
            "[e",
            vec![
                bracket_recovery::close(0, 2..2, None),
                (StructuralKind::Missing, (2)..(2)),
            ],
        ),
    ] {
        let (green, _, facts) = run_type_with_structural_diagnostics(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(facts, expected, "{source:?}");
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
    let (green, exit, facts) = run_type_with_structural_diagnostics(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(facts, [(StructuralKind::ErrorGroup, 2..3)]);
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
    let (green, exit, facts) = run_type_with_structural_diagnostics(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(facts, [(StructuralKind::ErrorGroup, 2..5)]);
    let tag = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
        .expect("multi-Item same-slot recovered tag");
    let children = tag.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children[0].kind(), SyntaxKind::Error);
    assert_eq!(children[0].to_string(), "@");
    assert_eq!(children[1].kind(), SyntaxKind::Error);
    assert_eq!(children[1].to_string(), " ");
    assert_eq!(children[2].kind(), SyntaxKind::Error);
    assert_eq!(children[2].to_string(), ".");
    assert_eq!(children[3].kind(), SyntaxKind::Whitespace);
    assert_eq!(children[3].to_string(), " ");
    assert_eq!(children[4].kind(), SyntaxKind::Identifier);
    assert_eq!(children[4].to_string(), "A");
    let groups = recovery_groups(&tag);
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0].text(), "@ .");
    assert_eq!(
        groups[0].text_range(),
        rowan::TextRange::new(2.into(), 5.into())
    );
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
        let errors = recovery_groups(&tag)
            .into_iter()
            .filter(|group| group.parent().as_ref() == Some(&tag))
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
        recovery_groups(&variant)
            .into_iter()
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
            recovery_groups(&variant)
                .into_iter()
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
    let errors = recovery_groups(&tags[0])
        .into_iter()
        .filter(|group| group.parent().as_ref() == Some(&tags[0]))
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
    let error = recovery_groups(&tag)
        .into_iter()
        .find(|group| group.parent().as_ref() == Some(&tag))
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
        recovery_groups(&variant)
            .into_iter()
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["@"]
    );

    for (source, emitted, leading) in [(":{@\n B}", ":{@", "\n "), (":{@\r\n B}", ":{@", "\r\n ")] {
        assert_polymorphic_variant_deep_newline_boundary(source, emitted, leading, Some("@"));
    }

    let (green, exit) = run_type(":{@;A}");
    assert_eq!(green.to_string(), ":{@;A}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    assert_eq!(
        recovery_groups(&variant)
            .into_iter()
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
        recovery_groups(&variant)
            .into_iter()
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
        let error = recovery_groups(&payload)
            .into_iter()
            .find(|group| group.parent().as_ref() == Some(&payload))
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
            recovery_groups(&payload)
                .into_iter()
                .filter(|group| group.parent().as_ref() == Some(&payload))
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
            let error = recovery_groups(&variant)
                .into_iter()
                .find(|group| {
                    group.parent().as_ref() == Some(&variant) && group.text() == separator
                })
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

    for (source, emitted, leading) in [
        (":{A @\n B}", ":{A @", "\n "),
        (":{A @\r\n B}", ":{A @", "\r\n "),
    ] {
        assert_polymorphic_variant_deep_newline_boundary(source, emitted, leading, Some("@"));
    }

    for (source, boundary) in [(":{A @;B}", ";"), (":{A @]}", "]")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = polymorphic_variant_node(green);
        let owner = if boundary == "]" {
            variant
                .children()
                .find(|node| node.kind() == SyntaxKind::PolymorphicVariantForeignClose)
                .expect("local foreign close slot")
        } else {
            variant.clone()
        };
        let error = recovery_groups(&owner)
            .into_iter()
            .find(|group| group.parent().as_ref() == Some(&owner) && group.text() == boundary)
            .expect("local payload boundary error");
        assert_eq!(
            error.parent().map(|node| node.kind()),
            Some(if boundary == "]" {
                SyntaxKind::PolymorphicVariantForeignClose
            } else {
                SyntaxKind::PolymorphicVariantType
            }),
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
        recovery_groups(&payload)
            .into_iter()
            .filter(|group| group.parent().as_ref() == Some(&payload))
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["@"]
    );
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("outer call");
    assert!(
        delimited_slot_children(&call)
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );
    assert!(
        delimited_slot_children(&call)
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
        let error = recovery_groups(&variant)
            .into_iter()
            .next()
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
        let error = recovery_groups(&variant)
            .into_iter()
            .next()
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
            .descendants_with_tokens()
            .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
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
        let errors = recovery_groups(&variant)
            .into_iter()
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
            let closes: Vec<_> = record
                .children()
                .filter(|node| node.kind() == SyntaxKind::NamedRecordTypeClose)
                .collect();
            assert_eq!(closes.len(), 1);
            assert_eq!(
                closes[0]
                    .children_with_tokens()
                    .map(|element| element.kind())
                    .collect::<Vec<_>>(),
                [SyntaxKind::Missing]
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
                .descendants_with_tokens()
                .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
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
                .any(|token| token.text() == ";"
                    && token.kind()
                        == if outer == SyntaxKind::NamedRecordType {
                            SyntaxKind::Error
                        } else {
                            SyntaxKind::Semicolon
                        }),
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
    let foreign_close = variant
        .children()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantForeignClose)
        .expect("local foreign close slot");
    let error = recovery_groups(&foreign_close)
        .into_iter()
        .find(|group| group.parent().as_ref() == Some(&foreign_close))
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
        delimited_slot_children(&call)
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

    for (source, emitted, leading) in [
        (":{A\n  B}", ":{A", "\n  "),
        (":{A\r\n  B}", ":{A", "\r\n  "),
    ] {
        assert_polymorphic_variant_deep_newline_boundary(source, emitted, leading, None);
    }
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
            recovery_groups(&top)
                .into_iter()
                .filter(|group| group.parent().as_ref() == Some(&top))
                .count(),
            1,
            "{source:?}"
        );
    }

    assert_complete_type_recovery("[e][f", 0, &[leading_row_recovery::head_error(0, 3..5)]);
}

#[test]
fn leading_bracket_row_retries_malformed_heads_without_a_missing_cascade() {
    for source in ["[e] @ T", "[e] @"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let top = top_type_expression(&green);
        assert_eq!(
            recovery_groups(&top)
                .into_iter()
                .filter(|group| group.parent().as_ref() == Some(&top))
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
        assert_eq!(recovery_groups(&root).into_iter().count(), 1, "{source:?}");
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
    let error = recovery_groups(&SyntaxNode::new_root(green))
        .into_iter()
        .next()
        .expect("bracket item error");
    assert_eq!(error.text().to_string(), "@");

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

    let (green, exit, facts) = run_type_with_structural_diagnostics("T [e\n  @]");
    assert_eq!(green.to_string(), "T [e");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert_eq!(
        facts,
        [
            bracket_recovery::close(0, 4..4, None),
            bracket_arrow_recovery::arrow(1, 4..4, false),
        ]
    );
    let root = SyntaxNode::new_root(green);
    assert!(
        !root
            .descendants_with_tokens()
            .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );
}

#[test]
fn bracket_row_recovery_keeps_item_and_close_slots_distinct() {
    for (source, error_text, missing) in [
        ("T [:] -> U", ":", 0),
        ("T [@\nA] -> U", "@", 0),
        ("T [@\n  A] -> U", "@", 0),
        ("T [A\n  )] -> U", ")", 0),
        ("T [@/* comment */A] -> U", "@", 0),
        ("T [@/*\n*/A] -> U", "@", 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let errors = recovery_groups(&root).into_iter().collect::<Vec<_>>();
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
    assert!(!root.descendants_with_tokens().any(|node| matches!(
        node.kind(),
        SyntaxKind::Error | SyntaxKind::Invalid | SyntaxKind::Missing
    )));

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
        ("T [e,)] -> U", &[")"][..], 1),
        ("T [@,)] -> U", &["@", ")"][..], 1),
        ("T [e))] -> U", &[")", ")"][..], 0),
        ("T [e))", &[")", ")"][..], 2),
        ("T [)", &[")"][..], 3),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            recovery_groups(&root)
                .into_iter()
                .map(|group| group.text())
                .collect::<Vec<_>>(),
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
        let (green, exit, facts) = run_type_with_structural_diagnostics(source);
        assert_eq!(green.to_string(), parsed, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Left(_)))), "{source:?}");
        assert_eq!(
            facts,
            [
                bracket_recovery::close(0, 4..5, Some(Delimiter::Parenthesis)),
                bracket_recovery::close(1, 5..5, None),
                bracket_arrow_recovery::arrow(2, 5..5, false),
            ]
        );
        let root = SyntaxNode::new_root(green);
        assert_eq!(recovery_groups(&root).into_iter().count(), 1, "{source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            2,
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
    assert_eq!(recovery_groups(&root).into_iter().count(), 1);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );
}

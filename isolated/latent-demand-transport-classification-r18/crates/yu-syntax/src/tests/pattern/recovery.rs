use crate::tests::pattern::*;
use crate::tests::recovery_output::recovery_groups;
use crate::tests::support::{StructuralFact, structural_facts};
use crate::{
    ambient_claim::AmbientClaimView,
    lexical::lexer::{scan_identifier, scan_pattern_payload},
    pattern::PATTERN_STOP_IN,
    structural_diagnostic::StructuralKind,
};
use chasa_recover::Recoverable as _;

mod default_expression;
mod delimited;
mod sequence;

#[derive(Clone, Copy)]
struct Context<'fence> {
    origin: usize,
    stops: PatternStops,
    policy: PatternMandatorySlotPolicy,
    closes: PatternCallerCloses,
    line: LineEntry,
    fence: Option<&'fence FenceBoundary>,
    emit_leading: bool,
}

impl Default for Context<'_> {
    fn default() -> Self {
        Self {
            origin: 0,
            stops: PATTERN_DEFAULT_STOPS,
            policy: PatternMandatorySlotPolicy::default(),
            closes: PatternCallerCloses::NONE,
            line: LineEntry::InLine,
            fence: None,
            emit_leading: false,
        }
    }
}

struct PatternRun<'source> {
    green: GreenNode,
    exit: NormalizedExit,
    completion: PatternCompletion,
    remainder: &'source str,
    successor: usize,
    facts: Vec<StructuralFact>,
}

const SENTINEL: &str = "sentinel";

fn fact(error: bool, range: std::ops::Range<usize>) -> StructuralFact {
    (
        if error {
            StructuralKind::ErrorGroup
        } else {
            StructuralKind::Missing
        },
        SENTINEL.len() + range.start..SENTINEL.len() + range.end,
    )
}

fn invalid_fact(range: std::ops::Range<usize>) -> StructuralFact {
    (
        StructuralKind::Invalid,
        SENTINEL.len() + range.start..SENTINEL.len() + range.end,
    )
}

fn publish_seed(output: &mut GreenNodeBuilder) {
    output.start_node(SyntaxKind::Missing.into());
    output.finish_node();
}

fn run<'source>(source: &'source str, context: Context<'_>) -> PatternRun<'source> {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mark = crate::cursor::LexRecover::new_for_test(recover.operators()).mark();
    let mut input = source;
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    output.token(SyntaxKind::Identifier.into(), SENTINEL);
    publish_seed(&mut output);
    let CurrentItem {
        mut item,
        next_line_entry,
    } = current_item(
        chasa_recover::In::new(
            &mut input,
            &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
            (),
        ),
        context.origin,
        context.line,
        context.fence,
        |mut lex, leading, origin, fence, _| {
            scan_pattern_literal_payload(lex.rb())
                .or_else(|| scan_pattern_nud_payload(lex, leading, origin, fence, context.stops))
        },
    )
    .unwrap();
    if context.emit_leading {
        item.emit_all_remaining_leading(&mut output);
    }
    let next = context.origin + source.len() - input.len();
    let (exit, completion) = required_pattern_from_entry_item_with_policy_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        item,
        0,
        context.stops,
        StatementLineHandoff::OrdinaryLayout,
        context.policy,
        context.closes,
        next,
        next_line_entry,
        context.fence,
        Some(AmbientClaimView::root_statement(0)).into(),
    );
    assert_eq!(
        crate::cursor::LexRecover::new_for_test(recover.operators()).mark(),
        mark
    );
    assert!(std::ptr::eq(recover.operators(), &operators));
    output.finish_node();
    let green = finish_with_discarded_recoveries(output, recover);
    let facts = structural_facts(&green);
    PatternRun {
        green,
        exit,
        completion,
        remainder: input,
        successor: context.origin + source.len() - input.len(),
        facts,
    }
}

fn assert_same_exit(left: &NormalizedExit, right: &NormalizedExit) {
    match (left, right) {
        (
            NormalizedExit::Complete(Err(Either::Left(a)), la),
            NormalizedExit::Complete(Err(Either::Left(b)), lb),
        ) => {
            assert_eq!(a, b);
            assert_eq!(la, lb);
        }
        (
            NormalizedExit::Complete(Err(Either::Right(a)), la),
            NormalizedExit::Complete(Err(Either::Right(b)), lb),
        ) => {
            assert_eq!(a, b);
            assert_eq!(la, lb);
        }
        _ => panic!("Pattern must return the same full current Item/EOF"),
    }
}

fn checked<'source>(
    source: &'source str,
    context: Context<'_>,
    expected: &[StructuralFact],
    emitted: &str,
    completion: PatternCompletion,
) -> PatternRun<'source> {
    let mut all = vec![(StructuralKind::Missing, SENTINEL.len()..SENTINEL.len())];
    all.extend_from_slice(expected);
    let fresh = run(source, context);
    assert_eq!(
        fresh.green.to_string(),
        format!("sentinel{emitted}"),
        "{source:?}"
    );
    assert_eq!(fresh.facts, all, "{source:?}");
    assert_eq!(fresh.completion, completion, "{source:?}");
    let root = SyntaxNode::new_root(fresh.green.clone());
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        all.iter()
            .filter(|(kind, _)| *kind == StructuralKind::Missing)
            .count(),
        "{source:?}\n{root:#?}"
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );
    for (_, fact_range) in all
        .iter()
        .filter(|(kind, _)| *kind == StructuralKind::ErrorGroup)
    {
        let range = rowan::TextRange::new(
            (fact_range.start as u32).into(),
            (fact_range.end as u32).into(),
        );
        if root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Invalid && node.text_range() == range)
        {
            continue;
        }
        let tokens = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| {
                token.kind() == SyntaxKind::Error && range.contains_range(token.text_range())
            })
            .collect::<Vec<_>>();
        assert!(!tokens.is_empty(), "{source:?}: {range:?}\n{root:#?}");
        assert_eq!(tokens[0].text_range().start(), range.start());
        assert_eq!(tokens.last().unwrap().text_range().end(), range.end());
        assert_eq!(
            tokens.iter().map(|token| token.text()).collect::<String>(),
            source[fact_range.start - SENTINEL.len()..fact_range.end - SENTINEL.len()]
        );
        for pair in tokens.windows(2) {
            assert_eq!(pair[0].parent(), pair[1].parent());
            assert_eq!(pair[0].text_range().end(), pair[1].text_range().start());
            assert_eq!(
                pair[0].next_sibling_or_token(),
                Some(pair[1].clone().into())
            );
        }
    }
    fresh
}

#[test]
fn primary_missing_preserves_the_immediate_cst_slot_without_remapping_children() {
    for origin in [0, 41] {
        for (source, at, emitted, complete) in [
            ("", 0, "", false),
            (" ", 0, "", false),
            ("A as", 4, "A as", false),
            (":", 1, ":", false),
            (": x", 1, ":", false),
            ("A |", 3, "A |", false),
            ("A | | B", 4, "A | | B", true),
            ("A | :", 5, "A | :", false),
            ("A as | B", 4, "A as | B", true),
        ] {
            checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &[fact(false, at..at)],
                emitted,
                if complete {
                    PatternCompletion::Complete
                } else {
                    PatternCompletion::Incomplete
                },
            );
        }
        let source = "A | @ :";
        checked(
            source,
            Context {
                origin,
                ..Context::default()
            },
            &[fact(true, 4..5), fact(false, 7..7)],
            source,
            PatternCompletion::Complete,
        );
    }
}

#[test]
fn primary_error_runs_exclude_retry_leading_and_keep_native_payloads() {
    for origin in [0, 41] {
        for (source, start, malformed, owner) in [
            ("@ x", 0, "@", SyntaxKind::Pattern),
            ("@ ? /*é*/ x", 0, "@ ?", SyntaxKind::Pattern),
            (" /*é*/ @ x", 0, " /*é*/ @", SyntaxKind::Pattern),
            ("A as @ x", 5, "@", SyntaxKind::PatternAliasTail),
            ("A as $x 1 @ x", 5, "$x 1 @", SyntaxKind::PatternAliasTail),
            ("A | @ ? x", 4, "@ ?", SyntaxKind::Pattern),
            ("A as @\r\n  x", 5, "@", SyntaxKind::PatternAliasTail),
        ] {
            let fresh = checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &[fact(true, start..start + malformed.len())],
                source,
                PatternCompletion::Complete,
            );
            assert_eq!(fresh.remainder, "");
            let root = SyntaxNode::new_root(fresh.green);
            let error = recovery_groups(&root).into_iter().next().unwrap();
            assert_eq!(error.to_string(), malformed);
            assert_eq!(error.parent().unwrap().kind(), owner);
            let retry_gap = error.next_sibling_or_token().unwrap();
            assert!(matches!(
                retry_gap.kind(),
                SyntaxKind::Whitespace | SyntaxKind::Newline
            ));
            assert_eq!(retry_gap.parent().unwrap().kind(), owner);
            if malformed == "$x 1 @" {
                assert_eq!(
                    error
                        .children_with_tokens()
                        .map(|element| element.kind())
                        .collect::<Vec<_>>(),
                    [SyntaxKind::Error; 5]
                );
                assert_eq!(
                    error
                        .children_with_tokens()
                        .map(|element| element.to_string())
                        .collect::<Vec<_>>(),
                    ["$x", " ", "1", " ", "@"]
                );
            }
        }
    }
}

fn assert_pending_control(run: &PatternRun<'_>, suffix: &str, origin: usize, context: Context<'_>) {
    let operators = OperatorTable::empty();
    let recover = Recover::new_for_test(&operators);
    let mut input = suffix;
    let current = current_item(
        chasa_recover::In::new(
            &mut input,
            &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
            (),
        ),
        origin,
        LineEntry::InLine,
        context.fence,
        |lex, leading, at, fence, _| scan_pattern_payload(lex, leading, at, fence, context.stops),
    )
    .unwrap();
    let expected = crate::handoff::complete(
        crate::handoff::handoff(current.item),
        current.next_line_entry,
    );
    assert_same_exit(&run.exit, &expected);
    assert_eq!(run.remainder, input);
    assert_eq!(run.successor, origin + suffix.len() - input.len());
}

#[test]
fn primary_and_alias_recovery_preserve_complete_caller_items_and_remaining_start() {
    for origin in [0, 41] {
        for (prefix, range, error) in [
            ("", 0..0, false),
            ("@", 0..1, true),
            ("A as", 4..4, false),
            ("A as @", 5..6, true),
            ("A |", 3..3, false),
            ("A | @", 4..5, true),
        ] {
            for suffix in [" /*é*/ )tail", "\r\n]tail", " }tail"] {
                let source = format!("{prefix}{suffix}");
                let context = Context {
                    origin,
                    closes: PatternCallerCloses::RPAREN
                        .union(PatternCallerCloses::RBRACKET)
                        .union(PatternCallerCloses::RBRACE),
                    ..Context::default()
                };
                let fresh = checked(
                    &source,
                    context,
                    &[fact(error, range.clone())],
                    prefix,
                    PatternCompletion::Incomplete,
                );
                assert_pending_control(&fresh, suffix, origin + prefix.len(), context);
            }
        }
        for emit_leading in [false, true] {
            let source = " /*é*/ =tail";
            let at = if emit_leading {
                source.find('=').unwrap()
            } else {
                0
            };
            let context = Context {
                origin,
                emit_leading,
                ..Context::default()
            };
            let fresh = checked(
                source,
                context,
                &[fact(false, at..at)],
                &source[..at],
                PatternCompletion::Incomplete,
            );
            let NormalizedExit::Complete(Err(Either::Left(mut item)), _) = fresh.exit else {
                panic!("pending Equals")
            };
            assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Equals));
            assert_eq!(
                emit_pending_leading_text(&mut item),
                if emit_leading { "" } else { " /*é*/ " }
            );
        }
    }
}

#[test]
fn alias_error_retry_checks_layout_and_in_before_accepting_a_name() {
    for suffix in ["\nx", "\r\nx", " /*é*/ in tail"] {
        let source = format!("A as @{suffix}");
        let context = Context {
            stops: PATTERN_DEFAULT_STOPS | PATTERN_STOP_IN,
            ..Context::default()
        };
        let fresh = checked(
            &source,
            context,
            &[fact(true, 5..6)],
            "A as @",
            PatternCompletion::Incomplete,
        );
        assert_pending_control(&fresh, suffix, 6, context);
    }
    // A fresh binding and a retried same-line `as` are ordinary identifiers.
    for source in ["A as\nx", "A as\r\nx", "A as as"] {
        checked(
            source,
            Context::default(),
            &[],
            source,
            PatternCompletion::Complete,
        );
    }
    checked(
        "A as @ as",
        Context::default(),
        &[fact(true, 5..6)],
        "A as @ as",
        PatternCompletion::Complete,
    );
}

#[test]
fn primary_tail_slots_preserve_quoted_fence_coordinates_before_and_after_error() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for origin in [0, 8_000] {
        for (prefix, error_range) in [
            ("", None),
            ("@", Some(0..1)),
            ("A as", None),
            ("A as @", Some(5..6)),
            ("A |", None),
            ("A | @", Some(4..5)),
        ] {
            let suffix = "\r\n> > ```\r\nouter";
            let source = format!("{prefix}{suffix}");
            let context = Context {
                origin,
                fence: Some(&fence),
                ..Context::default()
            };
            let error = error_range.is_some();
            let range = error_range.unwrap_or(prefix.len()..prefix.len());
            let fresh = checked(
                &source,
                context,
                &[fact(error, range)],
                prefix,
                PatternCompletion::Incomplete,
            );
            assert_pending_control(&fresh, suffix, origin + prefix.len(), context);
            let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart) =
                fresh.exit
            else {
                panic!("quoted fence pending")
            };
            assert_eq!(
                item.payload_view().pending_boundary().unwrap().coordinate(),
                origin + prefix.len() + 2
            );
        }
    }
}

#[test]
fn symbol_name_probe_rejection_preserves_seeded_output_and_cursor() {
    for source in ["", " x", "$x", "1", "@", "\r\n> > ```"] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new_for_test(&operators);
        let mut input = source;
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        output.token(SyntaxKind::Identifier.into(), SENTINEL);
        publish_seed(&mut output);
        let mark = crate::cursor::LexRecover::new_for_test(recover.operators()).mark();
        let mut probe: SyntaxIn =
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output);
        let name = probe.token(scan_identifier);
        assert!(name.is_none(), "{source:?}");
        assert_eq!(input.as_ptr(), source.as_ptr());
        assert_eq!(input, source);
        assert_eq!(
            crate::cursor::LexRecover::new_for_test(recover.operators()).mark(),
            mark
        );
        assert!(std::ptr::eq(recover.operators(), &operators));
        output.finish_node();
        let green = finish_with_discarded_recoveries(output, recover);
        assert_eq!(green.to_string(), SENTINEL);
        assert_eq!(structural_facts(&green), [(StructuralKind::Missing, 8..8)]);
        assert_eq!(recovery_count(&green, SyntaxKind::Missing), 1);
    }
}

#[test]
fn symbol_name_missing_has_a_direct_colon_successor_slot() {
    for source in [":", ": x"] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), ":");
        assert_eq!(structural_facts(&green), [(StructuralKind::Missing, 1..1)]);
        let pattern = pattern_node(green);
        let pattern_children = pattern.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(pattern_children.len(), 1);
        let symbol = pattern_children[0].as_node().expect("SymbolPattern");
        assert_eq!(symbol.kind(), SyntaxKind::SymbolPattern);
        assert_eq!(symbol.parent(), Some(pattern.clone()));
        let children = symbol.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), 2);
        let colon = children[0].as_token().expect("committed colon");
        assert_eq!(colon.kind(), SyntaxKind::Colon);
        assert_eq!(colon.text(), ":");
        assert_eq!(usize::from(colon.text_range().start()), 0);
        assert_eq!(usize::from(colon.text_range().end()), 1);
        assert_eq!(colon.parent().as_ref(), Some(symbol));
        let missing = children[1].as_node().expect("SymbolName Missing");
        assert_eq!(missing.kind(), SyntaxKind::Missing);
        assert_eq!(missing.parent().as_ref(), Some(symbol));
        assert_eq!(usize::from(missing.text_range().start()), 1);
        assert_eq!(usize::from(missing.text_range().end()), 1);
        assert_eq!(missing.children_with_tokens().count(), 0);
        assert_eq!(missing.to_string(), "");

        if source == ": x" {
            let Err(Either::Left(mut item)) = exit else {
                panic!("Identifier x remains pending")
            };
            assert_eq!(token_kind(&item), Some(TokenKind::Identifier));
            assert_eq!(item.payload_view().spelling(), Some("x"));
            assert_eq!(emit_pending_leading_text(&mut item), " ");
        } else {
            assert!(matches!(exit, Err(Either::Right(_))));
        }
    }
}

#[test]
fn alias_binding_recovery_has_a_direct_ordered_tail_slot() {
    for (source, expected, fact) in [
        (
            "A as",
            vec![
                (SyntaxKind::AsKw, 2..4, "as", true),
                (SyntaxKind::Missing, 4..4, "", false),
            ],
            (StructuralKind::Missing, 4..4),
        ),
        (
            "A as @ x",
            vec![
                (SyntaxKind::AsKw, 2..4, "as", true),
                (SyntaxKind::Whitespace, 4..5, " ", true),
                (SyntaxKind::Error, 5..6, "@", true),
                (SyntaxKind::Whitespace, 6..7, " ", true),
                (SyntaxKind::Identifier, 7..8, "x", true),
            ],
            (StructuralKind::ErrorGroup, 5..6),
        ),
        (
            "A as @",
            vec![
                (SyntaxKind::AsKw, 2..4, "as", true),
                (SyntaxKind::Whitespace, 4..5, " ", true),
                (SyntaxKind::Error, 5..6, "@", true),
            ],
            (StructuralKind::ErrorGroup, 5..6),
        ),
    ] {
        let (green, _) = run_pattern(source);
        assert_eq!(green.to_string(), source);
        assert_eq!(structural_facts(&green), [fact]);
        let pattern = pattern_node(green);
        let pattern_children = pattern.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(pattern_children.len(), 3, "{source}");
        let gap = pattern_children[1].as_token().expect("pre-as whitespace");
        assert_eq!(gap.kind(), SyntaxKind::Whitespace);
        assert_eq!(gap.text(), " ");
        assert_eq!(usize::from(gap.text_range().start()), 1);
        assert_eq!(usize::from(gap.text_range().end()), 2);
        assert_eq!(gap.parent(), Some(pattern.clone()));
        let tail = pattern_children[2].as_node().expect("PatternAliasTail");
        assert_eq!(tail.kind(), SyntaxKind::PatternAliasTail);
        assert_eq!(tail.parent(), Some(pattern.clone()));
        let children = tail.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), expected.len(), "{source}");
        for (child, (kind, range, text, token)) in children.iter().zip(expected) {
            assert_eq!(child.kind(), kind, "{source}");
            assert_eq!(usize::from(child.text_range().start()), range.start);
            assert_eq!(usize::from(child.text_range().end()), range.end);
            assert_eq!(child.to_string(), text);
            assert_eq!(child.as_token().is_some(), token);
            assert_eq!(child.parent().as_ref(), Some(tail));
            if let Some(missing) = child.as_node() {
                assert_eq!(missing.children_with_tokens().count(), 0);
            }
        }
    }
}

#[test]
fn accepted_primary_and_tail_controls_have_no_new_recovery() {
    // Authority: Pattern primary/symbol/fixed-tail grammar and its current
    // delimiter and Type-annotation addenda, not parser success as an oracle.
    for source in [
        "x",
        "$x",
        "1",
        ":x",
        "as",
        "A as x",
        "A | B as c",
        "A as x | B",
        "()",
        "(a,b,)",
        "[a,..b]",
        "{a:b}",
        "x: T",
    ] {
        let fresh = checked(
            source,
            Context::default(),
            &[],
            source,
            PatternCompletion::Complete,
        );
        assert_eq!(fresh.remainder, "");
        assert_eq!(fresh.successor, source.len());
        assert!(matches!(
            fresh.exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
    }
    for source in [":x", "as", "x"] {
        checked(
            source,
            Context {
                stops: PATTERN_STOP_COLON,
                ..Context::default()
            },
            &[],
            source,
            PatternCompletion::Complete,
        );
    }
}

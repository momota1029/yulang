use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView,
    handoff::MlMode,
    sequence::{SequenceContext, SequenceOwner},
    statement::StatementLineHandoff,
    structural_diagnostic::{StructuralDiagnostic, StructuralKind},
};

fn parse<'s>(
    source: &'s str,
    sequence: SequenceContext,
    origin: usize,
) -> (
    GreenNode,
    Vec<StructuralDiagnostic>,
    NormalizedExit,
    &'s str,
) {
    parse_fenced(source, sequence, origin, None)
}

fn parse_fenced<'s>(
    source: &'s str,
    sequence: SequenceContext,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> (
    GreenNode,
    Vec<StructuralDiagnostic>,
    NormalizedExit,
    &'s str,
) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = source;
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let exit = expr_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
        sequence,
    )
    .unwrap();
    output.finish_node();
    let green = output.finish();
    let records = structural_diagnostics(&green);
    (green, records, exit, input)
}

fn arguments(green: &GreenNode) -> Vec<usize> {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .filter(|n| n.kind() == SyntaxKind::ColonApplicationTail)
        .map(|n| {
            n.children()
                .filter(|n| n.kind() == SyntaxKind::OperatorChain)
                .count()
        })
        .collect()
}

#[test]
fn ownerless_colon_owns_comma_and_layout_newline_episodes() {
    for source in [
        "f: a, b",
        "f: a\nb",
        "f: a,\nb",
        "f: a\n, b",
        "f: a\n,\nb",
        "f: a\r\nb",
    ] {
        let (green, records, _, rest) = parse(source, None, 0);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(arguments(&green), [2], "{source:?}");
        assert!(records.is_empty(), "{source:?}: {records:?}");
        assert_eq!(rest, "");
    }
    let (green, records, _, _) = parse("f: a\n  b", None, 0);
    assert_eq!(arguments(&green), [1]);
    assert!(records.is_empty());
}

#[test]
fn every_explicit_owner_returns_the_whole_outer_comma_and_newline_item() {
    use SequenceOwner::*;
    for owner in [
        RootStatement,
        VirtualStatement,
        RecordPattern,
        RuleExpressionList,
        Parenthesized,
        Call,
        Index,
        ProjectionTuple,
        ProjectionRecord,
        Colon,
        IndentedStatement,
        BracedStatement,
        CaseInline,
        CaseIndented,
        CatchInline,
        CatchIndented,
        CatchBraced,
        If,
    ] {
        for (source, kind, range, rest) in [
            ("f: a , b", TokenKind::Comma, 4..6, " b"),
            ("f: a\r\n界", TokenKind::Identifier, 4..9, ""),
        ] {
            let (green, records, exit, remaining) = parse(source, Some(owner), 0);
            assert_eq!(green.to_string(), "f: a", "{owner:?} {source:?}");
            assert_eq!(arguments(&green), [1]);
            assert!(records.is_empty());
            let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                panic!("whole pending Item")
            };
            assert_eq!(token_kind(&item), Some(kind));
            assert_eq!(
                item.extent(source.len() - remaining.len()).recovery_range(),
                range
            );
            assert_eq!(remaining, rest);
        }
    }
}

#[test]
fn accepted_delimiters_replace_and_restore_the_callers_sequence() {
    for source in [
        "(f: a\nb)",
        "g(f: a\nb)",
        "g[f: a\nb]",
        "g.(f: a\nb)",
        "g.{f: a\nb}",
    ] {
        let (green, records, _, _) = parse(source, None, 0);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(arguments(&green), [1], "{source:?}");
        assert!(records.is_empty(), "{source:?}: {records:?}");
    }
    for (source, counts) in [
        ("(x): a, b", vec![2]),
        ("f: g: a, b", vec![2, 1]),
        ("f: (g: a, b), c", vec![2, 1]),
    ] {
        let (green, records, _, _) = parse(source, None, 0);
        assert_eq!(green.to_string(), source);
        assert_eq!(arguments(&green), counts);
        assert!(records.is_empty());
    }
}

#[test]
fn immediate_post_colon_newline_precedes_local_comma_recovery() {
    for source in ["f:\n, x", "f:\r\nx"] {
        let (green, records, exit, remaining) = parse(source, None, 0);
        assert_eq!(green.to_string(), "f:");
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].kind(), StructuralKind::Missing);
        assert_eq!(records[0].range(), &(2..2));
        let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
            panic!("pending newline Item")
        };
        assert_eq!(
            item.extent(source.len() - remaining.len())
                .recovery_range()
                .start,
            2
        );
        assert!(item.leading_view().has_ordinary_newline());
    }
    let (green, records, _, _) = parse("f:\n  a\n  b", None, 0);
    assert_eq!(green.to_string(), "f:\n  a\n  b");
    assert!(records.is_empty());
}

#[test]
fn lexical_error_retry_obeys_owned_and_protected_boundaries_in_cst_output() {
    for (source, sequence, text) in [
        ("f: @\r\n界", None, "f: @\r\n界"),
        ("f: @, x", None, "f: @, x"),
        ("f: @\r\n界", Some(SequenceOwner::RootStatement), "f: @"),
        ("f: @, x", Some(SequenceOwner::RootStatement), "f: @"),
        ("f: @ ]", None, "f: @"),
    ] {
        let (green, records, _, _) = parse(source, sequence, 40);
        assert_eq!(green.to_string(), text, "{source:?}");
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].kind(), StructuralKind::ErrorGroup);
        assert_eq!(records[0].range(), &(3..4));
    }
}

#[test]
fn actual_virtual_interpolation_has_outer_colon_sequence_ownership() {
    for interior in [
        "f: a, b", "f: a\nb", "f: a; b", "f: a", "f: @, b", "f: @\nb",
    ] {
        for quote in ["\"", "\"\"\""] {
            let source = format!("{quote}%{{{interior}}}後{quote}");
            let (green, _, _, rest) = parse(&source, None, 0);
            assert_eq!(green.to_string(), source);
            assert_eq!(
                arguments(&green),
                if interior.contains('@') {
                    vec![0]
                } else {
                    vec![1]
                }
            );
            assert_eq!(rest, "");
        }
    }
}

#[test]
fn actual_statement_if_and_arm_owners_keep_colon_to_one_argument() {
    for source in [
        "{f: a\nb}",
        "case x: n -> f: a, m -> b",
        "case x:\n  n -> f: a\n  m -> b",
        "catch x: n -> f: a",
        "catch x:\n  n -> f: a\n  m -> b",
        "catch x {n -> f: a, m -> b}",
        "if x: f: a else: g: b",
    ] {
        let (green, records, _, _) = parse(source, None, 0);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(arguments(&green).iter().all(|n| *n == 1), "{source:?}");
        assert!(!arguments(&green).is_empty());
        assert!(records.is_empty(), "{source:?}: {records:?}");
    }
    let (green, records, _, _) = parse("g:\n  f: a\n  b", None, 0);
    assert_eq!(green.to_string(), "g:\n  f: a\n  b");
    assert_eq!(arguments(&green), [0, 1]);
    assert!(records.is_empty());
    let (green, exit) = run_statement("f: a, b");
    assert_eq!(green.to_string(), "f: a");
    assert_eq!(arguments(&green), [1]);
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
}

#[test]
fn record_pattern_defaults_establish_their_local_expression_owner() {
    for source in ["{x = f: a, y}", "{x = f: a\ny}", "{x = (f: a, b), y}"] {
        let (green, _) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(arguments(&green), [1]);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants_with_tokens()
                .any(|n| matches!(
                    n.kind(),
                    SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
                ))
        );
    }
}

#[test]
fn trailing_literal_comma_and_repeated_comma_keep_mandatory_slots() {
    for source in ["f: a,", "f: a,, b"] {
        let (green, records, _, _) = parse(source, None, 0);
        assert_eq!(green.to_string(), source);
        assert_eq!(records.len(), 1, "{source:?}");
        assert_eq!(records[0].kind(), StructuralKind::Missing);
    }
}

#[test]
fn trailing_implicit_boundary_preserves_trivia_without_a_missing_argument() {
    for source in ["f: a\n", "f: a\r\n", "f: @\n", "f: @\r\n"] {
        let (green, records, exit, remaining) = parse(source, None, 0);
        assert_eq!(green.to_string(), source);
        assert_eq!(remaining, "");
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
        assert!(
            records
                .iter()
                .all(|record| record.kind() == StructuralKind::ErrorGroup)
        );
        assert_eq!(records.len(), usize::from(source.contains('@')));
    }
}

#[test]
fn nested_virtual_colons_replace_and_restore_virtual_and_outer_owners() {
    for quote in ["\"", "\"\"\""] {
        let source = format!("{quote}%{{\"%{{g: a, b}}\"; f: c, d}}{quote}: e, z");
        let (green, records, _, remaining) = parse(&source, None, 0);
        assert_eq!(green.to_string(), source);
        assert_eq!(remaining, "");
        assert!(records.is_empty());
        assert_eq!(arguments(&green), [1, 1, 2]);
    }
}

#[test]
fn virtual_colon_errors_keep_close_eof_and_quoted_fence_structural_facts() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for quote in ["\"", "\"\"\""] {
        for suffix in [
            format!(" }}後{quote}"),
            String::new(),
            "\r\n> > ```\nouter".to_owned(),
        ] {
            let source = format!("{quote}%{{f: 💥{suffix}");
            let (green, records, exit, remaining) = parse_fenced(&source, None, 80, Some(&fence));
            let start = quote.len() + "%{f: ".len();
            assert_eq!(records[0].kind(), StructuralKind::ErrorGroup, "{source:?}");
            assert_eq!(records[0].range(), &(start..start + 4), "{source:?}");
            assert_eq!(
                records
                    .iter()
                    .filter(|record| record.kind() == StructuralKind::Missing)
                    .count(),
                usize::from(suffix.is_empty() || suffix.contains("```")) * 2,
                "{source:?}"
            );
            if suffix.contains("```") {
                assert_eq!(green.to_string(), format!("{quote}%{{f: 💥"));
                assert_eq!(remaining, "> > ```\nouter");
                let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart) =
                    exit
                else {
                    panic!("pending physical fence")
                };
                assert!(item.payload_view().is_boundary());
            } else {
                assert_eq!(green.to_string(), source);
                assert_eq!(remaining, "");
            }
        }
    }
}

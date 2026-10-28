use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView, handoff::MlMode, statement::StatementLineHandoff,
    structural_diagnostic::StructuralKind,
};

fn parse<'s>(
    source: &'s str,
    stops: Stops,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, NormalizedExit, &'s str) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let exit = expr_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        None,
        0,
        stops,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    )
    .unwrap();
    output.finish_node();
    (
        finish_with_discarded_recoveries(output, recover),
        exit,
        input,
    )
}

#[test]
fn fixed_tail_slots_publish_exact_structural_facts() {
    for (source, kind, range) in [
        ("x.", StructuralKind::Missing, 2..2),
        ("x.@", StructuralKind::ErrorGroup, 2..3),
        ("x::", StructuralKind::Missing, 3..3),
        ("x::  ", StructuralKind::Missing, 5..5),
        ("x::123", StructuralKind::ErrorGroup, 3..6),
        ("x. field", StructuralKind::Missing, 2..2),
        ("x:: 123", StructuralKind::ErrorGroup, 4..7),
        ("x::::name", StructuralKind::Missing, 3..3),
        ("x::::$name", StructuralKind::Missing, 3..3),
    ] {
        let (green, _, _) = parse(source, 0, 0, None);
        assert_eq!(structural_facts(&green), [(kind, range)], "{source:?}");
        assert_eq!(green.to_string(), source);
    }
}

#[test]
fn path_error_keeps_each_adjacent_sigil_retry_item() {
    for name in ["$name", "&name", "'name"] {
        let source = format!("x::123{name}");
        let (green, exit, remainder) = parse(&source, 0, 0, None);
        assert_eq!(
            structural_facts(&green),
            [(StructuralKind::ErrorGroup, 3..6)]
        );
        assert_eq!(green.to_string(), "x::123");
        let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
            panic!("sigil retry stays current")
        };
        assert_eq!(token_kind(&item), Some(TokenKind::SigilIdentifier));
        assert_eq!(item.payload_view().spelling(), Some(name));
        assert_eq!(item.extent(source.len()).recovery_range(), 6..source.len());
        assert_eq!(remainder, "");
    }
}

#[test]
fn fixed_tail_boundaries_keep_the_whole_item_before_and_after_error() {
    use crate::lexical::stops::{STOP_COMMA, STOP_LINE_BREAK};
    for (intro, bad) in [("x.", "@"), ("x::", "123")] {
        for (boundary, stops, kind) in [
            (",", STOP_COMMA, TokenKind::Comma),
            (":", STOP_COLON, TokenKind::Colon),
            (")", 0, TokenKind::RParen),
            ("]", 0, TokenKind::RBracket),
            ("}", 0, TokenKind::RBrace),
            ("else", STOP_ELSE, TokenKind::Identifier),
            (" else", STOP_ELSE, TokenKind::Identifier),
            ("\r\nname", STOP_LINE_BREAK, TokenKind::Identifier),
        ] {
            for malformed in ["", bad] {
                let source = format!("{intro}{malformed}{boundary}");
                let (green, exit, remainder) = parse(&source, stops, 40, None);
                let start = intro.len();
                let end = start + malformed.len();
                assert_eq!(
                    structural_facts(&green),
                    [(
                        if malformed.is_empty() {
                            StructuralKind::Missing
                        } else {
                            StructuralKind::ErrorGroup
                        },
                        start..end
                    )],
                    "{source:?}"
                );
                assert_eq!(green.to_string(), format!("{intro}{malformed}"));
                let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                    panic!("protected Item remains current: {source:?}")
                };
                assert_eq!(token_kind(&item), Some(kind));
                assert_eq!(
                    item.extent(40 + source.len()).recovery_range(),
                    40 + end..40 + source.len()
                );
                assert_eq!(remainder, "");
            }
        }
    }
}

#[test]
fn accepted_path_leading_and_names_remain_in_the_tail() {
    for source in [
        "x.foo::bar",
        "x:: $name",
        "x::\r\nname",
        "x::\n  &name",
        "x::'name",
    ] {
        let (green, _, _) = parse(source, 0, 0, None);
        assert_eq!(green.to_string(), source);
        assert!(structural_facts(&green).is_empty());
    }
}

#[test]
fn recovered_names_keep_fixed_and_unstopped_colon_continuations() {
    for (source, range) in [
        ("x.@: y", 2..3),
        ("x::123: y", 3..6),
        ("x.@.field", 2..3),
        ("x::123::name", 3..6),
    ] {
        let (green, _, _) = parse(source, 0, 0, None);
        assert_eq!(
            structural_facts(&green),
            [(StructuralKind::ErrorGroup, range)]
        );
        assert_eq!(green.to_string(), source);
    }
}

#[test]
fn fixed_tail_utf8_error_and_quoted_fence_have_physical_extents() {
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
    for (source, kind, range, emitted) in [
        ("x.\r\n> > ```\nouter", StructuralKind::Missing, 2..2, "x."),
        (
            "x::💥\r\n> > ```\nouter",
            StructuralKind::ErrorGroup,
            3..7,
            "x::💥",
        ),
    ] {
        let (green, exit, remainder) = parse(source, 0, 100, Some(&fence));
        assert_eq!(structural_facts(&green), [(kind, range)]);
        assert_eq!(green.to_string(), emitted);
        assert_eq!(remainder, "> > ```\nouter");
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Left(_)), LineEntry::PhysicalStart)
        ));
    }
}

#[test]
fn fixed_tail_recovery_keeps_threshold_ml_and_seeded_output() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "+",
        OperatorFixities::new().with_infix(BindingPower::scalar(20), BindingPower::scalar(21)),
    )])
    .unwrap();
    for (source, threshold, mode, expected_text, pending, range) in [
        (
            "x.@ + y",
            70,
            MlMode::All,
            "x.@",
            Some(TokenKind::Operator),
            2..3,
        ),
        ("x.@ + y", 0, MlMode::All, "x.@ + y", None, 2..3),
        (
            "x::123 name",
            0,
            MlMode::None,
            "x::123",
            Some(TokenKind::Identifier),
            3..6,
        ),
        ("x::123 name", 0, MlMode::All, "x::123 name", None, 3..6),
    ] {
        let mut input = source;
        let mut recover = Recover::new_for_test(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        output.token(SyntaxKind::Identifier.into(), "seed");
        let threshold = BindingPower::scalar(threshold);
        let exit = expr_normalized(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            Some(&threshold),
            0,
            0,
            mode,
            StatementLineHandoff::OrdinaryLayout,
            0,
            LineEntry::InLine,
            None,
            Some(AmbientClaimView::root_statement(0)).into(),
            None,
        )
        .unwrap();
        output.finish_node();
        let green = finish_with_discarded_recoveries(output, recover);
        assert_eq!(green.to_string(), format!("seed{expected_text}"));
        assert_eq!(
            structural_facts(&green),
            [(StructuralKind::ErrorGroup, 4 + range.start..4 + range.end)]
        );
        if let Some(kind) = pending {
            let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                panic!("same Item handoff")
            };
            assert_eq!(token_kind(&item), Some(kind));
            if kind == TokenKind::Operator {
                assert_eq!(input, " y");
            }
        }
    }
}

#[test]
fn rejected_or_line_deferred_fixed_tail_preserves_seeded_output_and_cursor() {
    use crate::lexical::stops::STOP_LINE_BREAK;
    use crate::{expression::tail_normalized, lexical::expression_item::expression_item};
    for (source, stops, kind) in [
        ("..rest", 0, TokenKind::Unknown),
        ("\n.field", STOP_LINE_BREAK, TokenKind::Dot),
        ("\n::name", STOP_LINE_BREAK, TokenKind::PathSeparator),
    ] {
        let mut control = None;
        let mut control_item = None;
        for attempt in [false, true] {
            let operators = OperatorTable::empty();
            let mut recover = Recover::new_for_test(&operators);
            let mut output = GreenNodeBuilder::new();
            output.start_node(SyntaxKind::Root.into());
            output.token(SyntaxKind::Identifier.into(), "seed");
            let mut input = source;
            let (item, origin, line) = expression_item(
                crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                OperatorSite::Led,
                0,
                LineEntry::InLine,
                None,
                0,
                stops,
            );
            assert_eq!(token_kind(&item), Some(kind));
            let remainder = input;
            if attempt {
                let exit = tail_normalized(
                    crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                    item,
                    None,
                    0,
                    stops,
                    MlMode::All,
                    StatementLineHandoff::OrdinaryLayout,
                    origin,
                    line,
                    None,
                    Some(AmbientClaimView::root_statement(0)).into(),
                    None,
                );
                let NormalizedExit::Complete(Err(Either::Left(item)), returned_line) = exit else {
                    panic!("fixed-tail entry must remain unread")
                };
                assert_eq!(&item, control_item.as_ref().unwrap());
                assert_eq!(returned_line, line);
            } else {
                control_item = Some(item);
            }
            assert_eq!(input, remainder);
            let mut input = "x.";
            expr_normalized(
                crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                None,
                0,
                0,
                MlMode::All,
                StatementLineHandoff::OrdinaryLayout,
                10,
                LineEntry::InLine,
                None,
                Some(AmbientClaimView::root_statement(0)).into(),
                None,
            )
            .unwrap();
            output.finish_node();
            let green = finish_with_discarded_recoveries(output, recover);
            let product = (green.clone(), structural_facts(&green));
            assert_eq!(product.0.to_string(), "seedx.");
            assert_eq!(product.1, [(StructuralKind::Missing, 6..6)]);
            if let Some(control) = &control {
                assert_eq!(&product, control);
            } else {
                control = Some(product);
            }
        }
    }
}

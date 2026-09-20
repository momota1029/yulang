use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView, handoff::MlMode, statement::StatementLineHandoff,
    structural_diagnostic::StructuralKind,
};
use std::ops::Range;

#[derive(Clone, Copy)]
enum Form {
    Group,
    Call,
    Index,
    Tuple,
    Record,
}

fn parse<'s>(
    source: &'s str,
    form: Form,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, NormalizedExit, &'s str) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let exit = crate::expression::delimited::delimited_items_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        match form {
            Form::Group => crate::expression::delimited::DelimitedOwner::Parenthesized,
            Form::Call => crate::expression::delimited::DelimitedOwner::Call,
            Form::Index => crate::expression::delimited::DelimitedOwner::Index,
            Form::Tuple => crate::expression::delimited::DelimitedOwner::ProjectionTuple,
            Form::Record => crate::expression::delimited::DelimitedOwner::ProjectionRecord,
        },
        0,
        0,
        if matches!(form, Form::Group) {
            MlMode::LayoutOnly
        } else {
            MlMode::All
        },
        StatementLineHandoff::OrdinaryLayout,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
    );
    output.finish_node();
    (
        finish_with_discarded_recoveries(output, recover),
        exit,
        input,
    )
}

fn structural_fact(kind: StructuralKind, range: Range<usize>) -> StructuralFact {
    (kind, range)
}

fn check(source: &str, form: Form, expected: Vec<StructuralFact>) {
    let (green, _, remainder) = parse(source, form, 0, None);
    assert_eq!(structural_facts(&green), expected, "{source:?}");
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
}

#[test]
fn all_descriptors_publish_structural_recovery_facts() {
    for (form, close) in [
        (Form::Group, ')'),
        (Form::Call, ')'),
        (Form::Index, ']'),
        (Form::Tuple, ')'),
        (Form::Record, '}'),
    ] {
        let missing = |range| structural_fact(StructuralKind::Missing, range);
        let error = |range| structural_fact(StructuralKind::ErrorGroup, range);
        check(&format!("{close}"), form, vec![]);
        check(&format!("x,y{close}"), form, vec![]);
        if !matches!(form, Form::Group) {
            check(&format!("x;y{close}"), form, vec![]);
        }
        check(&format!("1x{close}"), form, vec![missing(1..1)]);
        check(
            &format!(",,{close}"),
            form,
            vec![missing(0..0), missing(1..1)],
        );
        check(&format!("@ x{close}"), form, vec![error(0..1)]);
        check(&format!("@,{close}"), form, vec![error(0..1)]);
        check(&format!("@{close}"), form, vec![error(0..1)]);
        check(" ", form, vec![missing(1..1)]);
        check("@", form, vec![error(0..1), missing(1..1)]);
        check("", form, vec![missing(0..0)]);
        check(&format!("x @ y{close}"), form, vec![error(2..3)]);
        let wrong = if close == ']' { ')' } else { ']' };
        check(&format!(" {wrong}{close}"), form, vec![error(0..2)]);
    }
}

#[test]
fn parenthesized_semicolon_is_a_separator_error_in_every_phase() {
    let error = |range| structural_fact(StructuralKind::ErrorGroup, range);
    check(";x)", Form::Group, vec![error(0..1)]);
    check(";;)", Form::Group, vec![error(0..1), error(1..2)]);
    check("x;)", Form::Group, vec![error(1..2)]);
    check(
        "x y)",
        Form::Group,
        vec![structural_fact(StructuralKind::Missing, 1..1)],
    );
}

#[test]
fn record_spread_rhs_has_no_duplicate_missing_fact() {
    check(
        "..,}",
        Form::Record,
        vec![structural_fact(StructuralKind::Missing, 2..2)],
    );
    check(
        "..@ x}",
        Form::Record,
        vec![structural_fact(StructuralKind::ErrorGroup, 2..3)],
    );
    check(
        "..@,}",
        Form::Record,
        vec![structural_fact(StructuralKind::ErrorGroup, 2..3)],
    );
}

#[test]
fn lexical_errors_end_at_lf_and_crlf_implicit_separators() {
    for newline in ["\n", "\r\n"] {
        let source = format!("@{newline}@)");
        check(
            &source,
            Form::Group,
            vec![
                structural_fact(StructuralKind::ErrorGroup, 0..1),
                structural_fact(
                    StructuralKind::ErrorGroup,
                    1 + newline.len()..2 + newline.len(),
                ),
            ],
        );
    }
}

#[test]
fn delimited_fence_and_nonzero_utf8_extents_stay_physical() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::None,
        close_column: 0,
    };
    for form in [
        Form::Group,
        Form::Call,
        Form::Index,
        Form::Tuple,
        Form::Record,
    ] {
        let source = "é\r\n```\nouter";
        let (green, exit, remainder) = parse(source, form, 100, Some(&fence));
        assert_eq!(
            structural_facts(&green),
            [structural_fact(StructuralKind::Missing, 2..2)]
        );
        assert_eq!(green.to_string(), "é");
        assert_raw_slots(&SyntaxNode::new_root(green.clone()), &[]);
        assert_eq!(remainder, "```\nouter");
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Left(_)), LineEntry::PhysicalStart)
        ));
    }
}

fn full(source: &str) -> GreenNode {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let exit = expr_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    );
    assert!(exit.is_some());
    output.finish_node();
    finish_with_discarded_recoveries(output, recover)
}

#[test]
fn projection_delimited_missing_slots_are_distinguished_by_ordered_cst() {
    use SyntaxKind::*;
    let assert_children = |parent: &SyntaxNode, expected: &[(SyntaxKind, bool, Range<usize>)]| {
        let actual = parent.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(actual.len(), expected.len(), "{parent:#?}");
        for (child, (kind, node, range)) in actual.iter().zip(expected) {
            assert_eq!(child.parent(), Some(parent.clone()));
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *node);
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *range
            );
        }
    };
    for (_form, owner_kind, opening, closing, open, close) in [
        (Form::Tuple, ProjectionTupleTail, "(", ")", LParen, RParen),
        (Form::Record, ProjectionRecordTail, "{", "}", LBrace, RBrace),
    ] {
        for (body, has_close, slots) in [
            (
                ",a",
                true,
                vec![
                    (Missing, true, 3..3),
                    (Comma, false, 3..4),
                    (OperatorChain, true, 4..5),
                ],
            ),
            (
                "1x",
                true,
                vec![
                    (OperatorChain, true, 3..4),
                    (Missing, true, 4..4),
                    (OperatorChain, true, 4..5),
                ],
            ),
            (
                "a",
                false,
                vec![(OperatorChain, true, 3..4), (Missing, true, 4..4)],
            ),
            ("", true, vec![]),
            ("a", true, vec![(OperatorChain, true, 3..4)]),
        ] {
            let source = format!("x.{opening}{body}{}", if has_close { closing } else { "" });
            let green = full(&source);
            let root = SyntaxNode::new_root(green.clone());
            let end = source.len();
            assert_eq!(root.kind(), Root);
            assert!(root.parent().is_none());
            assert_eq!(root.to_string(), source);
            assert_children(&root, &[(OperatorChain, true, 0..end)]);
            let chain = root.first_child().unwrap();
            assert_children(
                &chain,
                &[
                    (IdentifierExpression, true, 0..1),
                    (owner_kind, true, 1..end),
                ],
            );
            assert_children(&chain.first_child().unwrap(), &[(Identifier, false, 0..1)]);
            let owner = chain.last_child().unwrap();
            let mut direct = vec![(Dot, false, 1..2), (open, false, 2..3)];
            direct.extend(slots);
            if has_close {
                direct.push((close, false, end - 1..end));
            }
            assert_children(&owner, &direct);
            for item in owner.children().filter(|node| node.kind() == OperatorChain) {
                let range = item.text_range();
                let range = usize::from(range.start())..usize::from(range.end());
                let (expression, token) = if body == "1x" && range.start == 3 {
                    (IntegerLiteral, Integer)
                } else {
                    (IdentifierExpression, Identifier)
                };
                assert_children(&item, &[(expression, true, range.clone())]);
                assert_children(&item.first_child().unwrap(), &[(token, false, range)]);
            }
            for element in root.descendants_with_tokens() {
                let range = element.text_range();
                assert_eq!(
                    element.to_string(),
                    source[usize::from(range.start())..usize::from(range.end())]
                );
                assert!(!matches!(
                    element.kind(),
                    Invalid
                        | Error
                        | IndexItem
                        | ProjectionRecordSpreadItem
                        | ExpressionDelimitedSeparator
                        | ExpressionDelimitedForeignClose
                ));
            }

            let expected = direct
                .iter()
                .filter(|(kind, _, _)| *kind == Missing)
                .map(|(_, _, range)| structural_fact(StructuralKind::Missing, range.clone()))
                .collect::<Vec<_>>();
            assert_eq!(structural_facts(&green), expected, "{source:?}");
        }
    }
}

#[test]
fn ordinary_delimited_missing_slots_are_distinguished_by_ordered_cst() {
    use SyntaxKind::*;
    let assert_children = |parent: &SyntaxNode, expected: &[(SyntaxKind, bool, Range<usize>)]| {
        let actual = parent.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(actual.len(), expected.len(), "{parent:#?}");
        for (child, (kind, node, range)) in actual.iter().zip(expected) {
            assert_eq!(child.parent(), Some(parent.clone()));
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *node);
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *range
            );
        }
    };
    for (form, owner_kind, prefix, open, close, closing) in [
        (
            Form::Group,
            ParenthesizedExpression,
            "",
            LParen,
            RParen,
            ")",
        ),
        (Form::Call, CallTail, "f", LParen, RParen, ")"),
        (Form::Index, IndexTail, "x", LBracket, RBracket, "]"),
    ] {
        let start = prefix.len();
        let item_kind = if matches!(form, Form::Index) {
            IndexItem
        } else {
            OperatorChain
        };
        for (body, has_close, slots) in [
            (
                ",a",
                true,
                vec![
                    (Missing, true, 1..1),
                    (Comma, false, 1..2),
                    (item_kind, true, 2..3),
                ],
            ),
            (
                "1x",
                true,
                vec![
                    (item_kind, true, 1..2),
                    (Missing, true, 2..2),
                    (item_kind, true, 2..3),
                ],
            ),
            (
                "a",
                false,
                vec![(item_kind, true, 1..2), (Missing, true, 2..2)],
            ),
            ("", true, vec![]),
            ("a", true, vec![(item_kind, true, 1..2)]),
        ] {
            let opening = if open == LBracket { "[" } else { "(" };
            let source = format!(
                "{prefix}{opening}{body}{}",
                if has_close { closing } else { "" }
            );
            let green = full(&source);
            let root = SyntaxNode::new_root(green.clone());
            let end = source.len();
            assert_eq!(root.kind(), Root);
            assert!(root.parent().is_none());
            assert_eq!(root.to_string(), source);
            assert_children(&root, &[(OperatorChain, true, 0..end)]);
            let chain = root.first_child().unwrap();
            let mut outer = vec![];
            if start != 0 {
                outer.push((IdentifierExpression, true, 0..1));
            }
            outer.push((owner_kind, true, start..end));
            assert_children(&chain, &outer);
            let owner = chain.last_child().unwrap();
            let mut direct = vec![(open, false, start..start + 1)];
            direct.extend(
                slots.into_iter().map(|(kind, node, range)| {
                    (kind, node, start + range.start..start + range.end)
                }),
            );
            if has_close {
                direct.push((close, false, end - 1..end));
            }
            assert_children(&owner, &direct);
            for element in root.descendants_with_tokens() {
                let range = element.text_range();
                assert_eq!(
                    element.to_string(),
                    source[usize::from(range.start())..usize::from(range.end())]
                );
                assert!(!matches!(
                    element.kind(),
                    Invalid
                        | Error
                        | ExpressionDelimitedSeparator
                        | ExpressionDelimitedForeignClose
                ));
            }
            for item in owner.children().filter(|node| node.kind() == item_kind) {
                if item_kind == IndexItem {
                    let range = item.text_range();
                    assert_children(
                        &item,
                        &[(
                            OperatorChain,
                            true,
                            usize::from(range.start())..usize::from(range.end()),
                        )],
                    );
                }
            }

            let expected = direct
                .iter()
                .filter(|(kind, _, _)| *kind == Missing)
                .map(|(_, _, range)| structural_fact(StructuralKind::Missing, range.clone()))
                .collect::<Vec<_>>();
            assert_eq!(structural_facts(&green), expected, "{source:?}");

            // The existing loop seam exposes its exact accepted-close/EOF handoff.
            let interior = &source[start + 1..];
            let (_, exit, remainder) = parse(interior, form, start + 1, None);
            assert_eq!(remainder, "");
            if has_close {
                assert!(matches!(
                    exit,
                    NormalizedExit::Complete(Ok(()), LineEntry::InLine)
                ));
            } else {
                let NormalizedExit::Complete(Err(Either::Right(end_item)), LineEntry::InLine) =
                    exit
                else {
                    panic!("EOF handoff: {source:?}")
                };
                assert!(end_item.item.payload_view().is_eof());
                let extent = end_item.item.extent(end);
                assert_eq!(extent.physical(), end..end);
                assert_eq!(extent.leading(), end..end);
                assert_eq!(extent.remaining(), end..end);
                assert_eq!(extent.payload(), end..end);
            }
        }
    }
}

#[test]
fn parenthesized_collision_literals_keep_distinct_raw_slots() {
    for (source, slot) in [
        ("(@)", SyntaxKind::Error),
        ("(;)", SyntaxKind::ExpressionDelimitedSeparator),
        ("(])", SyntaxKind::ExpressionDelimitedForeignClose),
    ] {
        let green = full(source);
        assert_eq!(
            structural_facts(&green),
            [structural_fact(StructuralKind::ErrorGroup, 1..2)],
            "{source:?}"
        );
        assert_eq!(green.to_string(), source, "{source:?}");

        let root = SyntaxNode::new_root(green.clone());
        let group = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ParenthesizedExpression)
            .expect("parenthesized expression");
        assert_eq!(
            group
                .children_with_tokens()
                .map(|element| {
                    (
                        element.kind(),
                        usize::from(element.text_range().start())
                            ..usize::from(element.text_range().end()),
                    )
                })
                .collect::<Vec<_>>(),
            [
                (SyntaxKind::LParen, 0..1),
                (slot, 1..2),
                (SyntaxKind::RParen, 2..3),
            ],
            "{source:?}"
        );
        let middle = group.children_with_tokens().nth(1).unwrap();
        let leaf = if slot == SyntaxKind::Error {
            middle
        } else {
            let wrapper = middle.as_node().expect("transparent raw slot");
            assert_eq!(wrapper.children_with_tokens().count(), 1);
            wrapper.children_with_tokens().next().unwrap()
        };
        let error = leaf
            .as_token()
            .expect("raw slot content remains an Error token");
        assert_eq!(error.kind(), SyntaxKind::Error, "{source:?}");
        assert_eq!(
            error.text_range(),
            rowan::TextRange::new(1.into(), 2.into())
        );
        assert!(
            !group
                .descendants_with_tokens()
                .any(|element| matches!(element.kind(), SyntaxKind::Missing | SyntaxKind::Invalid)),
            "{source:?}"
        );
    }
}

#[test]
fn expression_delimited_raw_item_separator_and_foreign_close_matrix() {
    for (form, owner, source, slot, range, direct) in [
        (
            Form::Group,
            SyntaxKind::ParenthesizedExpression,
            "(@)",
            SyntaxKind::Error,
            1..2,
            vec![
                (SyntaxKind::LParen, 0..1),
                (SyntaxKind::Error, 1..2),
                (SyntaxKind::RParen, 2..3),
            ],
        ),
        (
            Form::Group,
            SyntaxKind::ParenthesizedExpression,
            "(a @ b)",
            SyntaxKind::ExpressionDelimitedSeparator,
            3..4,
            vec![
                (SyntaxKind::LParen, 0..1),
                (SyntaxKind::OperatorChain, 1..2),
                (SyntaxKind::Whitespace, 2..3),
                (SyntaxKind::Error, 3..4),
                (SyntaxKind::OperatorChain, 4..6),
                (SyntaxKind::RParen, 6..7),
            ],
        ),
        (
            Form::Group,
            SyntaxKind::ParenthesizedExpression,
            "(])",
            SyntaxKind::ExpressionDelimitedForeignClose,
            1..2,
            vec![
                (SyntaxKind::LParen, 0..1),
                (SyntaxKind::Error, 1..2),
                (SyntaxKind::RParen, 2..3),
            ],
        ),
        (
            Form::Call,
            SyntaxKind::CallTail,
            "f(@)",
            SyntaxKind::Error,
            2..3,
            vec![
                (SyntaxKind::LParen, 1..2),
                (SyntaxKind::Error, 2..3),
                (SyntaxKind::RParen, 3..4),
            ],
        ),
        (
            Form::Call,
            SyntaxKind::CallTail,
            "f(a @ b)",
            SyntaxKind::ExpressionDelimitedSeparator,
            4..5,
            vec![
                (SyntaxKind::LParen, 1..2),
                (SyntaxKind::OperatorChain, 2..3),
                (SyntaxKind::Whitespace, 3..4),
                (SyntaxKind::Error, 4..5),
                (SyntaxKind::OperatorChain, 5..7),
                (SyntaxKind::RParen, 7..8),
            ],
        ),
        (
            Form::Call,
            SyntaxKind::CallTail,
            "f(])",
            SyntaxKind::ExpressionDelimitedForeignClose,
            2..3,
            vec![
                (SyntaxKind::LParen, 1..2),
                (SyntaxKind::Error, 2..3),
                (SyntaxKind::RParen, 3..4),
            ],
        ),
        (
            Form::Index,
            SyntaxKind::IndexTail,
            "x[@]",
            SyntaxKind::Error,
            2..3,
            vec![
                (SyntaxKind::LBracket, 1..2),
                (SyntaxKind::Error, 2..3),
                (SyntaxKind::RBracket, 3..4),
            ],
        ),
        (
            Form::Index,
            SyntaxKind::IndexTail,
            "x[a @ b]",
            SyntaxKind::ExpressionDelimitedSeparator,
            4..5,
            vec![
                (SyntaxKind::LBracket, 1..2),
                (SyntaxKind::IndexItem, 2..3),
                (SyntaxKind::Whitespace, 3..4),
                (SyntaxKind::Error, 4..5),
                (SyntaxKind::IndexItem, 5..7),
                (SyntaxKind::RBracket, 7..8),
            ],
        ),
        (
            Form::Index,
            SyntaxKind::IndexTail,
            "x[)]",
            SyntaxKind::ExpressionDelimitedForeignClose,
            2..3,
            vec![
                (SyntaxKind::LBracket, 1..2),
                (SyntaxKind::Error, 2..3),
                (SyntaxKind::RBracket, 3..4),
            ],
        ),
        (
            Form::Tuple,
            SyntaxKind::ProjectionTupleTail,
            "x.(@)",
            SyntaxKind::Error,
            3..4,
            vec![
                (SyntaxKind::Dot, 1..2),
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::Error, 3..4),
                (SyntaxKind::RParen, 4..5),
            ],
        ),
        (
            Form::Tuple,
            SyntaxKind::ProjectionTupleTail,
            "x.(a @ b)",
            SyntaxKind::ExpressionDelimitedSeparator,
            5..6,
            vec![
                (SyntaxKind::Dot, 1..2),
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::OperatorChain, 3..4),
                (SyntaxKind::Whitespace, 4..5),
                (SyntaxKind::Error, 5..6),
                (SyntaxKind::OperatorChain, 6..8),
                (SyntaxKind::RParen, 8..9),
            ],
        ),
        (
            Form::Tuple,
            SyntaxKind::ProjectionTupleTail,
            "x.(])",
            SyntaxKind::ExpressionDelimitedForeignClose,
            3..4,
            vec![
                (SyntaxKind::Dot, 1..2),
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::Error, 3..4),
                (SyntaxKind::RParen, 4..5),
            ],
        ),
        (
            Form::Record,
            SyntaxKind::ProjectionRecordTail,
            "x.{@}",
            SyntaxKind::Error,
            3..4,
            vec![
                (SyntaxKind::Dot, 1..2),
                (SyntaxKind::LBrace, 2..3),
                (SyntaxKind::Error, 3..4),
                (SyntaxKind::RBrace, 4..5),
            ],
        ),
        (
            Form::Record,
            SyntaxKind::ProjectionRecordTail,
            "x.{a @ b}",
            SyntaxKind::ExpressionDelimitedSeparator,
            5..6,
            vec![
                (SyntaxKind::Dot, 1..2),
                (SyntaxKind::LBrace, 2..3),
                (SyntaxKind::OperatorChain, 3..4),
                (SyntaxKind::Whitespace, 4..5),
                (SyntaxKind::Error, 5..6),
                (SyntaxKind::OperatorChain, 6..8),
                (SyntaxKind::RBrace, 8..9),
            ],
        ),
        (
            Form::Record,
            SyntaxKind::ProjectionRecordTail,
            "x.{)}",
            SyntaxKind::ExpressionDelimitedForeignClose,
            3..4,
            vec![
                (SyntaxKind::Dot, 1..2),
                (SyntaxKind::LBrace, 2..3),
                (SyntaxKind::Error, 3..4),
                (SyntaxKind::RBrace, 4..5),
            ],
        ),
    ] {
        let separator = slot == SyntaxKind::ExpressionDelimitedSeparator;
        let direct = direct
            .into_iter()
            .map(|(kind, range)| {
                (
                    if kind == SyntaxKind::Error {
                        slot
                    } else {
                        kind
                    },
                    range,
                )
            })
            .collect::<Vec<_>>();
        let green = full(source);
        assert_eq!(
            structural_facts(&green),
            [structural_fact(StructuralKind::ErrorGroup, range.clone())],
            "{source:?}"
        );
        assert_eq!(green.to_string(), source, "{source:?}");

        let root = SyntaxNode::new_root(green.clone());
        let owner_node = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("expression-delimited owner");
        assert_eq!(
            owner_node
                .children_with_tokens()
                .map(|element| {
                    (
                        element.kind(),
                        usize::from(element.text_range().start())
                            ..usize::from(element.text_range().end()),
                    )
                })
                .collect::<Vec<_>>(),
            direct,
            "{source:?}"
        );
        assert!(
            !owner_node
                .descendants_with_tokens()
                .any(|element| matches!(element.kind(), SyntaxKind::Missing | SyntaxKind::Invalid)),
            "{source:?}"
        );
        let error = owner_node
            .descendants_with_tokens()
            .find(|element| element.kind() == SyntaxKind::Error)
            .expect("owner-local raw Error");
        let error = error
            .as_token()
            .expect("owner-local raw Error must be a token");
        if slot == SyntaxKind::Error {
            assert_eq!(error.parent().unwrap(), owner_node);
        } else {
            let wrapper = error.parent().unwrap();
            assert_eq!(wrapper.kind(), slot);
            assert_eq!(wrapper.parent().unwrap(), owner_node);
            assert_eq!(wrapper.children_with_tokens().count(), 1);
            assert_eq!(wrapper.text_range(), error.text_range());
        }
        assert_eq!(
            error.text_range(),
            rowan::TextRange::new((range.start as u32).into(), (range.end as u32).into()),
            "{source:?}"
        );
        let admitted = owner_node
            .children()
            .filter(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::IndexItem | SyntaxKind::OperatorChain
                )
            })
            .collect::<Vec<_>>();
        if separator {
            assert_eq!(admitted.len(), 2, "{source:?}");
            assert!(
                admitted.iter().all(|node| node.kind()
                    == if matches!(form, Form::Index) {
                        SyntaxKind::IndexItem
                    } else {
                        SyntaxKind::OperatorChain
                    }),
                "{source:?}"
            );
        } else {
            assert!(admitted.is_empty(), "{source:?}");
        }
    }
}

#[test]
fn outer_index_close_survives_parenthesized_and_call_nesting() {
    for source in ["a[(f(x ]", "a[(f(@ ]"] {
        let green = full(source);
        let mut expected = vec![];
        if source.contains('@') {
            expected.push(structural_fact(StructuralKind::ErrorGroup, 5..6));
        }
        expected.extend([
            structural_fact(StructuralKind::Missing, 6..6),
            structural_fact(StructuralKind::Missing, 6..6),
        ]);
        assert_eq!(structural_facts(&green), expected, "{source:?}");
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green.clone());
        assert_raw_slots(&root, &[]);
        let bracket = root
            .descendants_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|it| it.kind() == SyntaxKind::RBracket)
            .unwrap();
        assert_eq!(bracket.parent().unwrap().kind(), SyntaxKind::IndexTail);
        let leading = bracket.prev_token().unwrap();
        assert_eq!(leading.text(), " ");
        assert_eq!(leading.parent().unwrap().kind(), SyntaxKind::IndexTail);
    }
}

fn assert_raw_slots(root: &SyntaxNode, expected: &[(SyntaxKind, Range<usize>, &str)]) {
    let wrappers = root
        .descendants()
        .filter(|node| {
            matches!(
                node.kind(),
                SyntaxKind::ExpressionDelimitedSeparator
                    | SyntaxKind::ExpressionDelimitedForeignClose
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(wrappers.len(), expected.len(), "{root:#?}");
    for (wrapper, (kind, range, text)) in wrappers.iter().zip(expected) {
        assert_eq!(wrapper.kind(), *kind);
        assert_eq!(
            usize::from(wrapper.text_range().start())..usize::from(wrapper.text_range().end()),
            *range
        );
        assert_eq!(wrapper.to_string(), *text);
        let children = wrapper.children_with_tokens().collect::<Vec<_>>();
        assert!(!children.is_empty());
        assert!(
            children
                .iter()
                .all(|child| { child.kind() == SyntaxKind::Error && child.as_token().is_some() })
        );
        assert_eq!(
            children.first().unwrap().text_range().start(),
            wrapper.text_range().start()
        );
        assert_eq!(
            children.last().unwrap().text_range().end(),
            wrapper.text_range().end()
        );
    }
}

#[test]
fn raw_slots_preserve_mixed_repeated_runs_and_recovered_phase_for_every_owner() {
    for (form, close, wrong) in [
        (Form::Group, ')', ']'),
        (Form::Call, ')', ']'),
        (Form::Index, ']', ')'),
        (Form::Tuple, ')', ']'),
        (Form::Record, '}', ')'),
    ] {
        // The foreign close preserves Separator, then Recovered, then Item.
        let source = format!("a{wrong}@{wrong}@,{wrong}@{close}");
        let (green, _, remainder) = parse(&source, form, 0, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(remainder, "");
        let root = SyntaxNode::new_root(green.clone());
        let wrong = wrong.to_string();
        assert_raw_slots(
            &root,
            &[
                (SyntaxKind::ExpressionDelimitedForeignClose, 1..2, &wrong),
                (SyntaxKind::ExpressionDelimitedSeparator, 2..3, "@"),
                (SyntaxKind::ExpressionDelimitedForeignClose, 3..4, &wrong),
                (SyntaxKind::ExpressionDelimitedForeignClose, 6..7, &wrong),
            ],
        );
        let direct = root
            .children_with_tokens()
            .filter(|child| child.kind() == SyntaxKind::Error)
            .map(|child| {
                usize::from(child.text_range().start())..usize::from(child.text_range().end())
            })
            .collect::<Vec<_>>();
        assert_eq!(direct, [4..5, 7..8]);
        assert_eq!(
            structural_facts(&green),
            [
                structural_fact(StructuralKind::ErrorGroup, 1..2),
                structural_fact(StructuralKind::ErrorGroup, 2..3),
                structural_fact(StructuralKind::ErrorGroup, 3..4),
                structural_fact(StructuralKind::ErrorGroup, 4..5),
                structural_fact(StructuralKind::ErrorGroup, 6..7),
                structural_fact(StructuralKind::ErrorGroup, 7..8),
            ],
            "{source:?}"
        );
    }
}

#[test]
fn raw_separator_slots_keep_semicolons_leading_comments_utf8_and_newline_retry() {
    for (source, expected, fact_ranges) in [
        (
            ";a;@;;)",
            vec![(0..1, ";"), (2..3, ";"), (4..5, ";"), (5..6, ";")],
            vec![0..1, 2..3, 3..4, 4..5, 5..6],
        ),
        ("a @ /*c*/ 💥 b)", vec![(2..14, "@ /*c*/ 💥")], vec![2..14]),
        ("a ;)", vec![(1..3, " ;")], vec![1..3]),
        ("a @\n@)", vec![(2..3, "@")], vec![2..3, 4..5]),
        ("a @\r\n@)", vec![(2..3, "@")], vec![2..3, 5..6]),
    ] {
        let (green, _, remainder) = parse(source, Form::Group, 0, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(remainder, "");
        let facts = fact_ranges
            .into_iter()
            .map(|range| structural_fact(StructuralKind::ErrorGroup, range))
            .collect::<Vec<_>>();
        assert_eq!(structural_facts(&green), facts, "{source:?}");
        assert_raw_slots(
            &SyntaxNode::new_root(green.clone()),
            &expected
                .into_iter()
                .map(|(range, text)| (SyntaxKind::ExpressionDelimitedSeparator, range, text))
                .collect::<Vec<_>>(),
        );
    }
    let green = full("x.{..@ x}");
    assert_eq!(
        structural_facts(&green),
        [structural_fact(StructuralKind::ErrorGroup, 5..6)]
    );
    let root = SyntaxNode::new_root(green);
    assert_raw_slots(&root, &[]);
    let error = root
        .descendants_with_tokens()
        .find(|child| child.kind() == SyntaxKind::Error)
        .unwrap();
    assert_eq!(
        error.parent().unwrap().kind(),
        SyntaxKind::ProjectionRecordSpreadItem
    );
}

#[test]
fn maximal_runs_preserve_initial_and_internal_leading_and_exact_spread_retry() {
    check(
        "  @ @ x)",
        Form::Call,
        vec![structural_fact(StructuralKind::ErrorGroup, 2..5)],
    );
    check(
        "@ ..x}",
        Form::Record,
        vec![structural_fact(StructuralKind::ErrorGroup, 0..1)],
    );
    check(
        "@.. x}",
        Form::Record,
        vec![structural_fact(StructuralKind::ErrorGroup, 0..1)],
    );
    check(
        "..@.. x}",
        Form::Record,
        vec![
            structural_fact(StructuralKind::ErrorGroup, 2..3),
            structural_fact(StructuralKind::Missing, 3..3),
        ],
    );
    for source in ["+.. x}", "..+.. x}"] {
        check(
            source,
            Form::Record,
            vec![structural_fact(
                StructuralKind::ErrorGroup,
                0..source.find(' ').unwrap(),
            )],
        );
    }
    check(
        ".. +.. x}",
        Form::Record,
        vec![structural_fact(StructuralKind::ErrorGroup, 3..6)],
    );
    check(
        "x @,)",
        Form::Call,
        vec![structural_fact(StructuralKind::ErrorGroup, 2..3)],
    );
    check(
        "x @",
        Form::Call,
        vec![
            structural_fact(StructuralKind::ErrorGroup, 2..3),
            structural_fact(StructuralKind::Missing, 3..3),
        ],
    );
    check(
        " ]",
        Form::Group,
        vec![
            structural_fact(StructuralKind::ErrorGroup, 0..2),
            structural_fact(StructuralKind::Missing, 2..2),
        ],
    );
}

#[test]
fn accepted_delimiters_shield_contextual_stops_and_keep_ml_items() {
    for source in [
        "a(x y)",
        "a[x y]",
        "a.(x y)",
        "a.{x y}",
        "(x,y)",
        "if f({x}): y",
        "if f(x: y): z",
        "f(if x: y)",
        "f(case x: _ -> y)",
        "f({for x in xs: y})",
    ] {
        let green = full(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(structural_facts(&green).is_empty(), "{source:?}");
        assert_raw_slots(&SyntaxNode::new_root(green.clone()), &[]);
        assert!(
            !SyntaxNode::new_root(green.clone())
                .descendants_with_tokens()
                .any(|node| matches!(
                    node.kind(),
                    SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
                )),
            "{source:?}"
        );
    }
}

#[test]
fn quoted_prefix_and_utf8_error_ranges_stay_physical() {
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
    let source = "@\r\n> > 💥)";
    let (green, exit, remainder) = parse(source, Form::Group, 100, Some(&fence));
    assert_eq!(
        structural_facts(&green),
        [
            structural_fact(StructuralKind::ErrorGroup, 0..1),
            structural_fact(StructuralKind::ErrorGroup, 7..11),
        ]
    );
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Ok(()), LineEntry::InLine)
    ));
    let root = SyntaxNode::new_root(green.clone());
    assert_raw_slots(&root, &[]);
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|node| node.into_token())
            .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
            .count(),
        1
    );
    assert_eq!(
        crate::tests::recovery_output::recovery_groups(&root)
            .into_iter()
            .map(|node| node.to_string())
            .collect::<Vec<_>>(),
        ["@", "💥"]
    );

    let source = "@\r\n> > ])";
    let (green, _, remainder) = parse(source, Form::Group, 100, Some(&fence));
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    assert_raw_slots(
        &SyntaxNode::new_root(green.clone()),
        &[(
            SyntaxKind::ExpressionDelimitedForeignClose,
            1..8,
            "\r\n> > ]",
        )],
    );
    assert_eq!(
        structural_facts(&green),
        [
            structural_fact(StructuralKind::ErrorGroup, 0..1),
            structural_fact(StructuralKind::ErrorGroup, 1..8),
        ]
    );
}

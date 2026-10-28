use crate::structural_diagnostic::StructuralKind;
use crate::tests::support::*;

fn declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::CastDeclaration)
        .expect("CastDeclaration")
}

fn count(node: &SyntaxNode, kind: SyntaxKind) -> usize {
    if kind == SyntaxKind::Error {
        return crate::tests::recovery_output::recovery_groups(node).len();
    }
    node.descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

fn token_count(node: &SyntaxNode, kind: SyntaxKind) -> usize {
    node.descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == kind)
        .count()
}

#[test]
fn cast_pattern_keeps_its_following_item_for_the_cast_owner() {
    use SyntaxKind::{CastPattern, Error, IdentifierPattern, LParen, Pattern, RParen, Whitespace};

    let source = "cast(f x): A;";
    let (green, exit, facts, remainder) = typed_cast(source, 0, 0, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    assert!(matches!(
        exit,
        Some(NormalizedExit::Complete(Err(Either::Right(_)), _))
    ));
    assert_eq!(facts, [structural_fact(StructuralKind::ErrorGroup, 7..8)]);
    let root = SyntaxNode::new_root(green);
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::PatternMlApplicationTail)
    );
    let cast_pattern = root
        .descendants()
        .find(|node| node.kind() == CastPattern)
        .expect("CastPattern");
    assert_eq!(
        cast_pattern
            .children_with_tokens()
            .map(|child| child.kind())
            .collect::<Vec<_>>(),
        [LParen, Pattern, Whitespace, Error, RParen]
    );
    let direct_pattern = cast_pattern
        .children()
        .find(|node| node.kind() == Pattern)
        .expect("direct Cast Pattern");
    assert_eq!(
        direct_pattern
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [IdentifierPattern]
    );
    let recovered_item = cast_pattern
        .children_with_tokens()
        .find(|child| child.kind() == Error)
        .and_then(|child| child.into_token())
        .expect("Cast-owned Item recovery");
    assert_eq!(recovered_item.text(), "x");
    assert_eq!(recovered_item.parent().as_ref(), Some(&cast_pattern));
}

#[test]
fn cast_nested_pattern_is_the_delimiter_scoped_ml_application_witness() {
    let source = "cast((f x)): A";
    let (green, exit, _, remainder) = typed_cast(source, 0, 0, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    assert!(matches!(
        exit,
        Some(NormalizedExit::Complete(Err(Either::Right(_)), _))
    ));
    let declaration = declaration(&green);
    let cast_pattern = declaration
        .children()
        .find(|node| node.kind() == SyntaxKind::CastPattern)
        .expect("CastPattern");
    assert_eq!(
        usize::from(cast_pattern.text_range().start())
            ..usize::from(cast_pattern.text_range().end()),
        4..11
    );
    let outer_pattern = cast_pattern
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("outer Pattern");
    assert_eq!(
        outer_pattern
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::ParenthesizedPattern]
    );
    let parenthesized = outer_pattern.first_child().expect("ParenthesizedPattern");
    assert_eq!(
        parenthesized
            .children_with_tokens()
            .map(|child| child.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::LParen, SyntaxKind::Pattern, SyntaxKind::RParen,]
    );
    let inner_pattern = parenthesized
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("inner Pattern");
    assert_eq!(
        inner_pattern
            .children_with_tokens()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierPattern,
            SyntaxKind::Whitespace,
            SyntaxKind::PatternMlApplicationTail,
        ]
    );
    assert_eq!(
        cast_pattern
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::PatternMlApplicationTail)
            .count(),
        1
    );
    assert_eq!(count(&cast_pattern, SyntaxKind::Missing), 0);
    assert_eq!(count(&cast_pattern, SyntaxKind::Error), 0);
    let application = cast_pattern
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PatternMlApplicationTail)
        .expect("inner application");
    assert_eq!(
        application
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Pattern]
    );
    let argument = application.first_child().expect("argument Pattern");
    assert_eq!(
        argument
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::IdentifierPattern]
    );
    assert_eq!(
        declaration
            .children()
            .find(|node| node.kind() == SyntaxKind::CastTarget)
            .expect("CastTarget")
            .to_string(),
        ": A"
    );
}

fn pending_item(exit: Option<NormalizedExit>) -> Item {
    match exit {
        Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) => item,
        Some(NormalizedExit::Complete(Err(Either::Right(end)), _)) => end.item,
        _ => panic!("Cast witness must return one pending Item"),
    }
}

fn typed_cast<'s>(
    source: &'s str,
    origin: usize,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> (
    GreenNode,
    Option<NormalizedExit>,
    Vec<StructuralFact>,
    &'s str,
) {
    typed_cast_at(source, origin, stops, LineEntry::InLine, fence)
}

fn typed_cast_at<'s>(
    source: &'s str,
    origin: usize,
    stops: Stops,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (
    GreenNode,
    Option<NormalizedExit>,
    Vec<StructuralFact>,
    &'s str,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = cast_declaration_witness(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
        0,
        stops,
        crate::statement::StatementLineHandoff::OrdinaryLayout,
        origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    let green = finish_with_discarded_recoveries(builder, recover);
    let facts = structural_facts(&green);
    (green, exit, facts, input)
}

fn structural_fact(kind: StructuralKind, range: std::ops::Range<usize>) -> StructuralFact {
    (kind, range)
}

#[test]
fn cast_body_structural_facts_are_exact() {
    for origin in [100, 12_000] {
        for (source, stops, kind, relative_range) in [
            ("cast(x): A =", 0, StructuralKind::Missing, 12..12),
            ("cast(x): A =   ", 0, StructuralKind::Missing, 15..15),
            ("cast(x): A = ;", 0, StructuralKind::Missing, 12..12),
            ("cast(x): A = ,", 0, StructuralKind::Missing, 12..12),
            ("cast(x): A = )", 0, StructuralKind::Missing, 12..12),
            ("cast(x): A = ]", 0, StructuralKind::Missing, 12..12),
            ("cast(x): A = }", 0, StructuralKind::Missing, 12..12),
            ("cast(x): A =\r\nnext", 0, StructuralKind::Missing, 12..12),
            (
                "cast(x): A = else",
                STOP_ELSE,
                StructuralKind::Missing,
                12..12,
            ),
            (
                "cast(x): A = @ value",
                0,
                StructuralKind::ErrorGroup,
                13..14,
            ),
            ("cast(x): A = @ )", 0, StructuralKind::ErrorGroup, 13..14),
            (
                "cast(x): A = @ 💥 value",
                0,
                StructuralKind::ErrorGroup,
                13..19,
            ),
            ("cast(x): A = @   ", 0, StructuralKind::ErrorGroup, 13..17),
            ("cast(x): A = @\r\n", 0, StructuralKind::ErrorGroup, 13..14),
        ] {
            let expected = structural_fact(kind, relative_range);
            let (_, _, facts, _) = typed_cast(source, origin, stops, None);
            assert_eq!(facts.first(), Some(&expected), "{source:?} at {origin}");
        }
    }
}

#[test]
fn cast_inline_body_direct_rowan_slot_order_and_ranges() {
    use SyntaxKind::{Error, Missing, OperatorChain, Whitespace};

    // Exact Equals establishes Body. Only its direct recovery children belong
    // to this slot; an admitted OperatorChain begins Expression ownership.
    for (source, stops, expected) in [
        ("cast(x): A =", 0, vec![(Missing, 12..12)]),
        ("cast(x): A = ;", 0, vec![(Missing, 12..12)]),
        ("cast(x): A = )", 0, vec![(Missing, 12..12)]),
        ("cast(x): A = else", STOP_ELSE, vec![(Missing, 12..12)]),
        ("cast(x): A =\nnext", 0, vec![(Missing, 12..12)]),
        ("cast(x): A =\r\nnext", 0, vec![(Missing, 12..12)]),
        ("cast(x): A =\r\n", 0, vec![(Missing, 12..12)]),
        (
            "cast(x): A =   ",
            0,
            vec![(Whitespace, 12..15), (Missing, 15..15)],
        ),
        (
            "cast(x): A = @",
            0,
            vec![(Whitespace, 12..13), (Error, 13..14)],
        ),
        (
            "cast(x): A = @   ",
            0,
            vec![(Whitespace, 12..13), (Error, 13..14), (Error, 14..17)],
        ),
        (
            "cast(x): A = @\r\n",
            0,
            vec![(Whitespace, 12..13), (Error, 13..14)],
        ),
        (
            "cast(x): A = @ )",
            0,
            vec![(Whitespace, 12..13), (Error, 13..14)],
        ),
        (
            "cast(x): A = @ ;",
            0,
            vec![(Whitespace, 12..13), (Error, 13..14)],
        ),
        (
            "cast(x): A = @ else",
            STOP_ELSE,
            vec![(Whitespace, 12..13), (Error, 13..14)],
        ),
        (
            "cast(x): A = @ 💥 value",
            0,
            vec![
                (Whitespace, 12..13),
                (Error, 13..14),
                (Error, 14..15),
                (Error, 15..19),
                (Whitespace, 19..20),
                (OperatorChain, 20..25),
            ],
        ),
        (
            "cast(x): A = @ value",
            0,
            vec![
                (Whitespace, 12..13),
                (Error, 13..14),
                (Whitespace, 14..15),
                (OperatorChain, 15..20),
            ],
        ),
        (
            "cast(x): A = value",
            0,
            vec![(Whitespace, 12..13), (OperatorChain, 13..18)],
        ),
    ] {
        let (green, _, _) = run_cast_declaration(source, stops, 0, LineEntry::InLine, None);
        let node = declaration(&green);
        let mut children = node.children_with_tokens();
        assert_eq!(children.next().unwrap().kind(), SyntaxKind::CastKw);
        assert_eq!(children.next().unwrap().kind(), SyntaxKind::CastPattern);
        assert_eq!(children.next().unwrap().kind(), SyntaxKind::CastTarget);
        assert_eq!(children.next().unwrap().kind(), Whitespace);
        let equals = children.next().unwrap();
        assert_eq!(equals.kind(), SyntaxKind::Equals);
        assert_eq!(
            equals.text_range(),
            rowan::TextRange::new(11.into(), 12.into())
        );
        let body = children.next().unwrap().into_node().unwrap();
        assert_eq!(body.kind(), SyntaxKind::CastBody);
        assert!(children.next().is_none());
        let actual = body
            .children_with_tokens()
            .map(|child| {
                match child.kind() {
                    Error | Whitespace => assert!(child.as_token().is_some()),
                    Missing | OperatorChain => assert!(child.as_node().is_some()),
                    _ => panic!("unexpected direct Body child in {source:?}"),
                }
                let range = child.text_range();
                (
                    child.kind(),
                    usize::from(range.start())..usize::from(range.end()),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(actual, expected, "{source:?}");
    }
}

#[test]
fn cast_inline_body_direct_rowan_boundary_leading_stays_pending() {
    for prefix in ["cast(x): A =", "cast(x): A = @"] {
        for (suffix, stops, kind, leading) in [
            (" ;", 0, Some(TokenKind::Semicolon), " "),
            (" )", 0, Some(TokenKind::RParen), " "),
            ("\r\n", 0, None, "\r\n"),
        ] {
            let source = format!("{prefix}{suffix}");
            let (green, exit, remainder) =
                run_cast_declaration(&source, stops, 0, LineEntry::InLine, None);
            assert_eq!(green.to_string(), prefix);
            assert_eq!(remainder, "");
            let mut pending = pending_item(exit);
            assert_eq!(pending.payload_view().token_kind(), kind);
            assert_eq!(emit_pending_leading_text(&mut pending), leading);
        }
    }
}

#[test]
fn cast_inline_body_direct_rowan_keeps_indented_statement_owner() {
    let source = "cast(x): A =\n  body";
    let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(remainder, "");
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    let mut after_equals = node
        .children_with_tokens()
        .skip_while(|child| child.kind() != SyntaxKind::Equals)
        .skip(1);
    let body = after_equals.next().unwrap().into_node().unwrap();
    assert_eq!(body.kind(), SyntaxKind::CastBody);
    assert!(after_equals.next().is_none());
    let children = body.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children.len(), 1);
    let owner = children[0].as_node().unwrap();
    assert_eq!(owner.kind(), SyntaxKind::IndentedStatementBlock);
    assert_eq!(owner.parent(), Some(body));
    assert!(
        owner
            .children()
            .any(|child| child.kind() == SyntaxKind::Statement)
    );
}
#[test]
fn cast_body_introducer_direct_rowan_slot_order_and_ranges() {
    use SyntaxKind::{
        CastBody, CastPattern, CastTarget, Equals, Error, Missing, Semicolon, Whitespace,
    };

    // Completed Pattern and Target children establish this slot. Native form
    // punctuation ends it; a protected handoff leaves no child in this owner.
    for (source, stops, expected) in [
        ("cast(x): A", 0, vec![(Missing, 10..10)]),
        ("cast(x): A )", 0, vec![(Missing, 10..10)]),
        ("cast(x): A ]", 0, vec![(Missing, 10..10)]),
        ("cast(x): A }", 0, vec![(Missing, 10..10)]),
        ("cast(x): A ,", 0, vec![(Missing, 10..10)]),
        ("cast(x): A else", STOP_ELSE, vec![(Missing, 10..10)]),
        ("cast(x): A\r\nvalue", 0, vec![(Missing, 10..10)]),
        ("cast(x): A;", 0, vec![(Semicolon, 10..11)]),
        (
            "cast(x): A= value",
            0,
            vec![(Equals, 10..11), (CastBody, 11..17)],
        ),
        (
            "cast(x): A @",
            0,
            vec![(Whitespace, 10..11), (Error, 11..12)],
        ),
        (
            "cast(x): A @   ",
            0,
            vec![(Whitespace, 10..11), (Error, 11..12), (Error, 12..15)],
        ),
        (
            "cast(x): A @\r\n  ",
            0,
            vec![(Whitespace, 10..11), (Error, 11..12)],
        ),
        (
            "cast(x): A @ )",
            0,
            vec![(Whitespace, 10..11), (Error, 11..12)],
        ),
        (
            "cast(x): A @ ,",
            0,
            vec![(Whitespace, 10..11), (Error, 11..12)],
        ),
        (
            "cast(x): A @ else",
            STOP_ELSE,
            vec![(Whitespace, 10..11), (Error, 11..12)],
        ),
        (
            "cast(x): A @ ;",
            0,
            vec![
                (Whitespace, 10..11),
                (Error, 11..12),
                (Whitespace, 12..13),
                (Semicolon, 13..14),
            ],
        ),
        (
            "cast(x): A @ = value",
            0,
            vec![
                (Whitespace, 10..11),
                (Error, 11..12),
                (Whitespace, 12..13),
                (Equals, 13..14),
                (CastBody, 14..20),
            ],
        ),
        (
            "cast(x): A @ # = value",
            0,
            vec![
                (Whitespace, 10..11),
                (Error, 11..12),
                (Error, 12..13),
                (Error, 13..14),
                (Whitespace, 14..15),
                (Equals, 15..16),
                (CastBody, 16..22),
            ],
        ),
    ] {
        let (green, _, _) = run_cast_declaration(source, stops, 0, LineEntry::InLine, None);
        let node = declaration(&green);
        let mut children = node.children_with_tokens();
        assert_eq!(children.next().unwrap().kind(), SyntaxKind::CastKw);
        let pattern = children.next().unwrap().into_node().unwrap();
        assert_eq!(pattern.kind(), CastPattern, "{source:?}");
        assert_eq!(pattern.last_token().unwrap().kind(), SyntaxKind::RParen);
        let target = children.next().unwrap().into_node().unwrap();
        assert_eq!(target.kind(), CastTarget, "{source:?}");
        assert_eq!(
            target.text_range(),
            rowan::TextRange::new(7.into(), 10.into())
        );
        let mut errors = Vec::new();
        let actual = children
            .map(|child| {
                let range = child.text_range();
                let range = usize::from(range.start())..usize::from(range.end());
                if child.kind() == Error {
                    assert!(child.as_token().is_some(), "{source:?}");
                    errors.push(range.clone());
                }
                (child.kind(), range)
            })
            .collect::<Vec<_>>();
        assert_eq!(actual, expected, "{source:?}");
        assert!(
            errors.windows(2).all(|pair| pair[0].end == pair[1].start),
            "{source:?}"
        );
        assert!(
            node.children_with_tokens()
                .all(|child| child.kind() != SyntaxKind::Invalid),
            "{source:?}"
        );
    }
}

#[test]
fn cast_body_introducer_direct_rowan_excludes_later_body_recovery() {
    use SyntaxKind::{CastBody, CastTarget, Equals, Error, Missing, Whitespace};

    let (green, _, _) = run_cast_declaration("cast(x): A @ =", 0, 0, LineEntry::InLine, None);
    let node = declaration(&green);
    let actual = node
        .children_with_tokens()
        .skip_while(|child| child.kind() != CastTarget)
        .skip(1)
        .map(|child| {
            let range = child.text_range();
            (
                child.kind(),
                usize::from(range.start())..usize::from(range.end()),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        actual,
        [
            (Whitespace, 10..11),
            (Error, 11..12),
            (Whitespace, 12..13),
            (Equals, 13..14),
            (CastBody, 14..14)
        ]
    );
    let body = node
        .children()
        .find(|child| child.kind() == CastBody)
        .unwrap();
    let missing = body
        .children()
        .find(|child| child.kind() == Missing)
        .expect("later Body Missing");
    assert_eq!(missing.parent(), Some(body));
    assert_eq!(
        missing.text_range(),
        rowan::TextRange::new(14.into(), 14.into())
    );
    assert!(
        node.children_with_tokens()
            .all(|child| child.kind() != SyntaxKind::Invalid)
    );
}

#[test]
fn cast_body_introducer_structural_facts_are_exact() {
    for origin in [100, 12_000] {
        for (source, stops, kind, relative_range) in [
            ("cast(x): A", 0, StructuralKind::Missing, 10..10),
            ("cast(x): A )", 0, StructuralKind::Missing, 10..10),
            ("cast(x): A ]", 0, StructuralKind::Missing, 10..10),
            ("cast(x): A }", 0, StructuralKind::Missing, 10..10),
            ("cast(x): A ,", 0, StructuralKind::Missing, 10..10),
            ("cast(x): A\r\nvalue", 0, StructuralKind::Missing, 10..10),
            (
                "cast(x): A else",
                STOP_ELSE,
                StructuralKind::Missing,
                10..10,
            ),
            ("cast(x): A @ ;", 0, StructuralKind::ErrorGroup, 11..12),
            (
                "cast(x): A @ = value",
                0,
                StructuralKind::ErrorGroup,
                11..12,
            ),
            (
                "cast(x): A @ # = value",
                0,
                StructuralKind::ErrorGroup,
                11..14,
            ),
            ("cast(x): A @ )", 0, StructuralKind::ErrorGroup, 11..12),
            ("cast(x): A @   ", 0, StructuralKind::ErrorGroup, 11..15),
            ("cast(x): A @\r\n", 0, StructuralKind::ErrorGroup, 11..12),
            ("cast(x): A @ あ ;", 0, StructuralKind::ErrorGroup, 11..16),
        ] {
            let expected = structural_fact(kind, relative_range);
            let (_, _, facts, _) = typed_cast(source, origin, stops, None);
            assert_eq!(facts.first(), Some(&expected), "{source:?} at {origin}");
        }
    }
}

#[test]
fn cast_target_introducer_structural_facts_are_exact() {
    for origin in [100, 12_000] {
        for (source, stops, kind, relative_range) in [
            ("cast(x)", 0, StructuralKind::Missing, 7..7),
            ("cast(x);", 0, StructuralKind::Missing, 7..7),
            ("cast(x)= value", 0, StructuralKind::Missing, 7..7),
            ("cast(x) T;", 0, StructuralKind::Missing, 8..8),
            ("cast(x) )", 0, StructuralKind::Missing, 7..7),
            ("cast(x) ]", 0, StructuralKind::Missing, 7..7),
            ("cast(x) }", 0, StructuralKind::Missing, 7..7),
            ("cast(x)\r\nT;", 0, StructuralKind::Missing, 7..7),
            ("cast(x) else", STOP_ELSE, StructuralKind::Missing, 7..7),
            ("cast(x) @ : T;", 0, StructuralKind::ErrorGroup, 8..9),
            ("cast(x) @ T;", 0, StructuralKind::ErrorGroup, 8..9),
            ("cast(x) @ ;", 0, StructuralKind::ErrorGroup, 8..9),
            ("cast(x) @ = value", 0, StructuralKind::ErrorGroup, 8..9),
            ("cast(x) @ )", 0, StructuralKind::ErrorGroup, 8..9),
            ("cast(x) @   ", 0, StructuralKind::ErrorGroup, 8..12),
            ("cast(x) @\r\n", 0, StructuralKind::ErrorGroup, 8..9),
            ("cast(x) @ あ T;", 0, StructuralKind::ErrorGroup, 8..9),
        ] {
            let expected = structural_fact(kind, relative_range);
            let (_, _, facts, _) = typed_cast(source, origin, stops, None);
            assert_eq!(facts.first(), Some(&expected), "{source:?} at {origin}");
        }
    }
}

#[test]
fn cast_target_introducer_direct_rowan_slot_order_and_ranges() {
    use SyntaxKind::{CastPattern, CastTarget, Equals, Error, Missing, Semicolon, Whitespace};

    // The completed parenthesized Pattern establishes the left slot boundary.
    // A target or form starter establishes the right boundary; outer boundaries
    // remain absent from this declaration's children.
    for (source, stops, expected) in [
        ("cast(x)", 0, vec![(Missing, 7..7)]),
        ("cast(x);", 0, vec![(Missing, 7..7), (Semicolon, 7..8)]),
        ("cast(x)= value", 0, vec![(Missing, 7..7), (Equals, 7..8)]),
        ("cast(x) )", 0, vec![(Missing, 7..7)]),
        ("cast(x) ]", 0, vec![(Missing, 7..7)]),
        ("cast(x) }", 0, vec![(Missing, 7..7)]),
        ("cast(x) else", STOP_ELSE, vec![(Missing, 7..7)]),
        ("cast(x)\r\nT;", 0, vec![(Missing, 7..7)]),
        (
            "cast(x) T;",
            0,
            vec![(Whitespace, 7..8), (CastTarget, 8..9)],
        ),
        ("cast(x) @", 0, vec![(Whitespace, 7..8), (Error, 8..9)]),
        (
            "cast(x) @   ",
            0,
            vec![(Whitespace, 7..8), (Error, 8..9), (Error, 9..12)],
        ),
        (
            "cast(x) @\r\n  ",
            0,
            vec![(Whitespace, 7..8), (Error, 8..9)],
        ),
        ("cast(x) @ )", 0, vec![(Whitespace, 7..8), (Error, 8..9)]),
        (
            "cast(x) @ else",
            STOP_ELSE,
            vec![(Whitespace, 7..8), (Error, 8..9)],
        ),
        (
            "cast(x) @ ;",
            0,
            vec![
                (Whitespace, 7..8),
                (Error, 8..9),
                (Whitespace, 9..10),
                (Semicolon, 10..11),
            ],
        ),
        (
            "cast(x) @ = value",
            0,
            vec![
                (Whitespace, 7..8),
                (Error, 8..9),
                (Whitespace, 9..10),
                (Equals, 10..11),
            ],
        ),
        (
            "cast(x) @ : T;",
            0,
            vec![
                (Whitespace, 7..8),
                (Error, 8..9),
                (Whitespace, 9..10),
                (CastTarget, 10..13),
            ],
        ),
        (
            "cast(x) @ T;",
            0,
            vec![
                (Whitespace, 7..8),
                (Error, 8..9),
                (Whitespace, 9..10),
                (CastTarget, 10..11),
            ],
        ),
        (
            "cast(x) @ @ T;",
            0,
            vec![
                (Whitespace, 7..8),
                (Error, 8..9),
                (Error, 9..10),
                (Error, 10..11),
                (Whitespace, 11..12),
                (CastTarget, 12..13),
            ],
        ),
    ] {
        let (green, _, _) = run_cast_declaration(source, stops, 0, LineEntry::InLine, None);
        let node = declaration(&green);
        let mut children = node.children_with_tokens();
        assert_eq!(children.next().expect("keyword").kind(), SyntaxKind::CastKw);
        let pattern = children
            .next()
            .expect("completed pattern")
            .into_node()
            .unwrap();
        assert_eq!(pattern.kind(), CastPattern, "{source:?}");
        assert_eq!(
            pattern.text_range(),
            rowan::TextRange::new(4.into(), 7.into())
        );
        assert_eq!(pattern.last_token().unwrap().kind(), SyntaxKind::RParen);
        let mut actual = Vec::new();
        let mut errors = Vec::new();
        for child in children {
            let kind = child.kind();
            let range = child.text_range();
            let range = usize::from(range.start())..usize::from(range.end());
            if kind == Error {
                assert!(child.as_token().is_some(), "{source:?}");
                errors.push(range.clone());
            }
            actual.push((kind, range));
            if matches!(kind, CastTarget | Semicolon | Equals) {
                break;
            }
        }
        assert_eq!(actual, expected, "{source:?}");
        if let (Some(first), Some(last)) = (errors.first(), errors.last()) {
            assert!(errors.windows(2).all(|pair| pair[0].end == pair[1].start));
            let expected_errors = expected
                .iter()
                .filter(|(kind, _)| *kind == Error)
                .collect::<Vec<_>>();
            assert_eq!(
                first.start..last.end,
                expected_errors.first().unwrap().1.start..expected_errors.last().unwrap().1.end,
                "{source:?}"
            );
        }
        assert!(
            node.children()
                .all(|child| child.kind() != SyntaxKind::Invalid),
            "{source:?}"
        );
    }
}

#[test]
fn cast_target_introducer_direct_rowan_active_rparen_stays_pending() {
    use SyntaxKind::{CastKw, CastPattern, CastTarget, Error, Invalid, Missing, TypeExpression};

    for (source, pending_leading) in [("cast(x)) tail", ""), ("cast(x) ) tail", " ")] {
        let stops = stops_for(TokenKind::RParen);
        let (green, exit, facts, remainder) = typed_cast(source, 0, stops, None);
        assert_eq!(green.to_string(), "cast(x)", "{source:?}");
        assert_eq!(remainder, " tail", "{source:?}");
        assert_eq!(
            facts,
            [structural_fact(StructuralKind::Missing, 7..7)],
            "{source:?}"
        );

        let node = declaration(&green);
        let mut children = node.children_with_tokens();
        let keyword = children.next().expect("direct keyword");
        assert_eq!(keyword.kind(), CastKw, "{source:?}");
        assert!(keyword.as_token().is_some(), "{source:?}");
        assert_eq!(
            keyword.text_range(),
            rowan::TextRange::new(0.into(), 4.into())
        );

        let pattern = children.next().expect("completed direct pattern");
        assert_eq!(pattern.kind(), CastPattern, "{source:?}");
        let pattern = pattern.as_node().expect("CastPattern is a node");
        assert_eq!(pattern.parent(), Some(node.clone()), "{source:?}");
        assert_eq!(
            pattern.text_range(),
            rowan::TextRange::new(4.into(), 7.into())
        );
        assert_eq!(pattern.last_token().unwrap().kind(), SyntaxKind::RParen);

        let missing = children.next().expect("direct target introducer Missing");
        assert_eq!(missing.kind(), Missing, "{source:?}");
        assert!(missing.as_node().is_some(), "{source:?}");
        assert_eq!(
            missing.text_range(),
            rowan::TextRange::new(7.into(), 7.into())
        );
        assert!(children.next().is_none(), "{source:?}");
        assert_eq!(count(&node, Missing), 1, "{source:?}");
        assert_eq!(count(&node, Error), 0, "{source:?}");
        assert!(
            !node
                .descendants()
                .any(|child| { matches!(child.kind(), CastTarget | TypeExpression | Invalid) }),
            "{source:?}"
        );

        let mut pending = pending_item(exit);
        assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::RParen));
        assert_eq!(emit_pending_leading_text(&mut pending), pending_leading);
    }
}

#[test]
fn cast_target_type_fresh_missing_has_direct_ordered_rowan_slot() {
    use SyntaxKind::*;

    let source = "cast(x): ;";
    let (green, exit, remainder) = run_statement_normalized(source, 0, LineEntry::InLine, None);
    let root = SyntaxNode::new_root(green.clone());
    assert_eq!(root.kind(), Root);
    assert_eq!(root.text().to_string(), source);
    assert_eq!(
        root.text_range(),
        rowan::TextRange::new(0.into(), 10.into())
    );
    assert_eq!(root.parent(), None);

    // The complete ordered inventory includes every node and token, with its
    // actual parent. It distinguishes fresh target absence from introducer
    // recovery and from recovery inside an accepted nested Type.
    let elements = root.descendants_with_tokens().collect::<Vec<_>>();
    let expected = [
        (Root, true, 0..10, None),
        (Statement, true, 0..10, Some(0)),
        (CastDeclaration, true, 0..10, Some(1)),
        (CastKw, false, 0..4, Some(2)),
        (CastPattern, true, 4..7, Some(2)),
        (LParen, false, 4..5, Some(4)),
        (Pattern, true, 5..6, Some(4)),
        (IdentifierPattern, true, 5..6, Some(6)),
        (Identifier, false, 5..6, Some(7)),
        (RParen, false, 6..7, Some(4)),
        (CastTarget, true, 7..9, Some(2)),
        (Colon, false, 7..8, Some(10)),
        (Whitespace, false, 8..9, Some(10)),
        (TypeExpression, true, 9..9, Some(10)),
        (Missing, true, 9..9, Some(13)),
        (Semicolon, false, 9..10, Some(2)),
    ];
    assert_eq!(elements.len(), expected.len());
    for (index, (element, (kind, is_node, range, parent))) in
        elements.iter().zip(&expected).enumerate()
    {
        assert_eq!(element.kind(), *kind, "element {index}");
        assert_eq!(element.as_node().is_some(), *is_node, "element {index}");
        assert_eq!(
            element.text_range(),
            rowan::TextRange::new((range.start as u32).into(), (range.end as u32).into()),
            "element {index}"
        );
        assert_eq!(
            element.to_string(),
            &source[range.clone()],
            "element {index}"
        );
        assert_eq!(
            element.parent(),
            parent.map(|parent| elements[parent].as_node().unwrap().clone()),
            "element {index}"
        );
        if let Some(node) = element.as_node() {
            let children = expected.iter().enumerate().filter_map(|(child, entry)| {
                (entry.3 == Some(index)).then(|| elements[child].clone())
            });
            assert_eq!(
                node.children_with_tokens().collect::<Vec<_>>(),
                children.collect::<Vec<_>>()
            );
        }
    }
    assert_eq!(count(&root, Missing), 1);
    assert!(
        !elements
            .iter()
            .any(|element| matches!(element.kind(), Error | Invalid))
    );
    let missing = elements[14].as_node().unwrap();
    assert!(missing.children_with_tokens().next().is_none());

    assert_eq!(
        structural_facts(&green),
        [structural_fact(StructuralKind::Missing, 9..9)]
    );
    let check_exit = |exit, remainder: &str| {
        assert_eq!(remainder, "");
        let NormalizedExit::Complete(Err(Either::Right(end)), LineEntry::InLine) = exit else {
            panic!("bodyless Cast must return the EOF Item in-line")
        };
        let mut item = end.item;
        assert!(item.payload_view().is_eof());
        assert_eq!(emit_pending_leading_text(&mut item), "");
    };
    check_exit(exit, remainder);
    let (fresh_green, fresh_exit, facts, fresh_remainder) = typed_cast(source, 0, 0, None);
    let typed_root = SyntaxNode::new_root(fresh_green.clone());
    assert_eq!(typed_root.kind(), Root);
    let typed_children = typed_root.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(typed_children.len(), 1);
    assert_eq!(typed_children[0].kind(), CastDeclaration);
    assert!(typed_children[0].as_node().is_some());
    assert_eq!(
        declaration(&fresh_green).green(),
        declaration(&green).green()
    );
    assert_eq!(facts, [structural_fact(StructuralKind::Missing, 9..9)]);
    check_exit(fresh_exit.unwrap(), fresh_remainder);
}

#[test]
fn cast_target_type_initial_error_has_direct_ordered_rowan_slots() {
    use SyntaxKind::*;

    // Only the initial required-Type run after a completed Pattern and actual
    // Colon belongs here. TargetIntroducer `cast(x) @ : T;` and recovery after
    // accepted Type `cast(x): A @ ;` are distinct slots outside this matrix.
    for (source, error_ranges, retry, target_end, declaration_leading) in [
        ("cast(x): @ ;", vec![9..10], None, 10, Some(10..11)),
        (
            "cast(x): @ T;",
            vec![9..10],
            Some((10..11, 11..12)),
            12,
            None,
        ),
        (
            "cast(x): @  ~   T;",
            vec![9..10, 10..12, 12..13],
            Some((13..16, 16..17)),
            17,
            None,
        ),
    ] {
        let (green, exit, remainder) = run_statement_normalized(source, 0, LineEntry::InLine, None);
        let root = SyntaxNode::new_root(green.clone());
        let end = source.len();
        let mut expected = vec![
            (Root, true, 0..end, None),
            (Statement, true, 0..end, Some(0)),
            (CastDeclaration, true, 0..end, Some(1)),
            (CastKw, false, 0..4, Some(2)),
            (CastPattern, true, 4..7, Some(2)),
            (LParen, false, 4..5, Some(4)),
            (Pattern, true, 5..6, Some(4)),
            (IdentifierPattern, true, 5..6, Some(6)),
            (Identifier, false, 5..6, Some(7)),
            (RParen, false, 6..7, Some(4)),
            (CastTarget, true, 7..target_end, Some(2)),
            (Colon, false, 7..8, Some(10)),
            (Whitespace, false, 8..9, Some(10)),
        ];
        expected.extend(
            error_ranges
                .iter()
                .cloned()
                .map(|range| (Error, false, range, Some(10))),
        );
        if let Some((leading, identifier)) = retry {
            let parent = expected.len();
            expected.extend([
                (
                    TypeExpression,
                    true,
                    leading.start..identifier.end,
                    Some(10),
                ),
                (Whitespace, false, leading, Some(parent)),
                (Identifier, false, identifier, Some(parent)),
            ]);
        }
        if let Some(leading) = declaration_leading {
            expected.push((Whitespace, false, leading, Some(2)));
        }
        expected.push((Semicolon, false, end - 1..end, Some(2)));
        let elements = root.descendants_with_tokens().collect::<Vec<_>>();
        assert_eq!(root.text().to_string(), source);
        assert_eq!(elements.len(), expected.len(), "{source:?}");
        for (index, (element, (kind, is_node, range, parent))) in
            elements.iter().zip(&expected).enumerate()
        {
            assert_eq!(element.kind(), *kind, "{source:?} element {index}");
            assert_eq!(element.as_node().is_some(), *is_node);
            assert_eq!(
                element.text_range(),
                rowan::TextRange::new((range.start as u32).into(), (range.end as u32).into())
            );
            assert_eq!(element.to_string(), &source[range.clone()]);
            assert_eq!(
                element.parent(),
                parent.map(|parent| elements[parent].as_node().unwrap().clone())
            );
            if let Some(node) = element.as_node() {
                let children = expected.iter().enumerate().filter_map(|(child, entry)| {
                    (entry.3 == Some(index)).then(|| elements[child].clone())
                });
                assert_eq!(
                    node.children_with_tokens().collect::<Vec<_>>(),
                    children.collect::<Vec<_>>()
                );
            }
        }

        // The completed Pattern and native
        // Colon locate the required-Type slot; its adjacent direct Error
        // leaves end at either the target frontier or the retry TypeExpression.
        let cast = elements[2].as_node().unwrap();
        let children = cast.children_with_tokens().collect::<Vec<_>>();
        let [keyword, pattern, target, ..] = children.as_slice() else {
            panic!("Cast requires its ordered prefix");
        };
        assert_eq!(keyword.kind(), CastKw);
        let pattern = pattern.as_node().unwrap();
        assert_eq!(pattern.kind(), CastPattern);
        assert_eq!(pattern.first_token().unwrap().kind(), LParen);
        assert_eq!(pattern.last_token().unwrap().kind(), RParen);
        let target = target.as_node().unwrap();
        assert_eq!(target.kind(), CastTarget);
        let target_children = target.children_with_tokens().collect::<Vec<_>>();
        let [colon, leading, malformed @ ..] = target_children.as_slice() else {
            panic!("required-Type slot follows actual Colon and native leading");
        };
        assert_eq!(colon.as_token().unwrap().kind(), Colon);
        assert_eq!(leading.as_token().unwrap().kind(), Whitespace);
        let group = malformed
            .iter()
            .take_while(|child| child.kind() == Error)
            .collect::<Vec<_>>();
        assert!(!group.is_empty());
        assert!(group.iter().all(|child| child.as_token().is_some()));
        for pair in group.windows(2) {
            assert_eq!(pair[0].text_range().end(), pair[1].text_range().start());
        }
        let range = rowan::TextRange::new(
            group.first().unwrap().text_range().start(),
            group.last().unwrap().text_range().end(),
        );
        match &malformed[group.len()..] {
            [] => assert_eq!(range.end(), target.text_range().end()),
            [retry] => {
                let retry = retry.as_node().unwrap();
                assert_eq!(retry.kind(), TypeExpression);
                assert_eq!(retry.text_range().start(), range.end());
                assert_eq!(retry.first_token().unwrap().kind(), Whitespace);
                assert_eq!(retry.text_range().end(), target.text_range().end());
            }
            _ => panic!("initial Error group ends before exactly one retry TypeExpression"),
        }
        assert!(
            !elements
                .iter()
                .any(|element| matches!(element.kind(), Missing | Invalid))
        );
        assert_eq!(
            elements
                .iter()
                .filter(|element| element.kind() == Error)
                .collect::<Vec<_>>(),
            group
        );
        let fact_range = usize::from(range.start())..usize::from(range.end());
        assert_eq!(
            fact_range,
            9..error_ranges.last().unwrap().end,
            "{source:?}"
        );
        assert_eq!(
            structural_facts(&green),
            [structural_fact(
                StructuralKind::ErrorGroup,
                fact_range.clone()
            )],
            "{source:?}"
        );
        let check_exit = |exit, remainder: &str| {
            assert_eq!(remainder, "");
            let NormalizedExit::Complete(Err(Either::Right(end)), LineEntry::InLine) = exit else {
                panic!("bodyless Cast must return EOF in-line");
            };
            let mut item = end.item;
            assert!(item.payload_view().is_eof());
            assert_eq!(emit_pending_leading_text(&mut item), "");
        };
        check_exit(exit, remainder);
        let (fresh_green, fresh_exit, facts, fresh_remainder) = typed_cast(source, 0, 0, None);
        let typed_root = SyntaxNode::new_root(fresh_green.clone());
        assert_eq!(typed_root.kind(), Root);
        let typed_children = typed_root.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(typed_children.len(), 1);
        assert_eq!(typed_children[0].kind(), CastDeclaration);
        assert!(typed_children[0].as_node().is_some());
        assert_eq!(declaration(&fresh_green).green(), cast.green());
        assert_eq!(
            facts,
            [structural_fact(StructuralKind::ErrorGroup, fact_range)],
            "{source:?}"
        );
        check_exit(fresh_exit.unwrap(), fresh_remainder);
    }
}

#[test]
fn cast_target_introducer_direct_target_children_distinguish_type_recovery() {
    use SyntaxKind::{CastTarget, Colon, Missing, TypeExpression, Whitespace};

    for (source, expected) in [
        (
            "cast(x): T;",
            vec![(Colon, 7..8), (Whitespace, 8..9), (TypeExpression, 9..10)],
        ),
        ("cast(x) T;", vec![(Missing, 8..8), (TypeExpression, 8..9)]),
        (
            "cast(x) @ : T;",
            vec![
                (Colon, 10..11),
                (Whitespace, 11..12),
                (TypeExpression, 12..13),
            ],
        ),
        ("cast(x) @ T;", vec![(TypeExpression, 10..11)]),
        ("cast(x) @ @ T;", vec![(TypeExpression, 12..13)]),
    ] {
        let (green, _, _) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        let node = declaration(&green);
        let target = node
            .children()
            .find(|child| child.kind() == CastTarget)
            .expect("direct target");
        assert_eq!(target.parent(), Some(node), "{source:?}");
        let actual = target
            .children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    usize::from(range.start())..usize::from(range.end()),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(actual, expected, "{source:?}");
    }

    let (green, _, _) = run_cast_declaration("cast(x): (T;", 0, 0, LineEntry::InLine, None);
    let node = declaration(&green);
    let target = node
        .children()
        .find(|child| child.kind() == CastTarget)
        .expect("direct target");
    assert_eq!(target.first_token().unwrap().kind(), Colon);
    assert!(
        target
            .children()
            .all(|child| child.kind() != Missing && child.kind() != SyntaxKind::Invalid)
    );
    let ty = target
        .children()
        .find(|child| child.kind() == TypeExpression)
        .expect("nested Type owner");
    assert!(ty.descendants().any(|child| child.kind() == Missing));
}

#[test]
fn cast_pattern_close_structural_facts_are_exact() {
    for origin in [100, 12_000] {
        for (source, kind, relative_range) in [
            ("cast(x", StructuralKind::Missing, 6..6),
            ("cast(x;", StructuralKind::Missing, 6..6),
            ("cast(x= value", StructuralKind::Missing, 6..6),
            ("cast(x @ ): T;", StructuralKind::ErrorGroup, 7..8),
            ("cast(x @ = value", StructuralKind::ErrorGroup, 7..8),
            ("cast(x @ =", StructuralKind::ErrorGroup, 7..8),
            ("cast(x @ == = value", StructuralKind::ErrorGroup, 7..11),
            ("cast(x @ =>> = value", StructuralKind::ErrorGroup, 7..12),
            ("cast(x @   ", StructuralKind::ErrorGroup, 7..11),
            ("cast(x @\r\n", StructuralKind::ErrorGroup, 7..8),
        ] {
            let expected = structural_fact(kind, relative_range);
            let (_, _, facts, _) = typed_cast(source, origin, 0, None);
            assert_eq!(facts.first(), Some(&expected), "{source:?} at {origin}");
        }
    }
}

#[test]
fn cast_pattern_close_direct_rowan_terminal_order_and_ranges() {
    use SyntaxKind::{Error, LParen, Missing, Pattern, RParen, Whitespace};

    // The completed Pattern separates terminal close recovery from value recovery.
    // Native retry leading is ordinary trivia, while same-line EOF leading
    // remains adjacent Error leaves in this close slot.
    for (source, stops, terminal) in [
        ("cast(x): T;", 0, vec![(RParen, 6..7)]),
        ("cast(x", 0, vec![(Missing, 6..6)]),
        ("cast(x;", 0, vec![(Missing, 6..6)]),
        ("cast(x= value", 0, vec![(Missing, 6..6)]),
        ("cast(x ] tail", 0, vec![(Missing, 6..6)]),
        ("cast(x } tail", 0, vec![(Missing, 6..6)]),
        ("cast(x else tail", STOP_ELSE, vec![(Missing, 6..6)]),
        ("cast(x @", 0, vec![(Whitespace, 6..7), (Error, 7..8)]),
        (
            "cast(x @   ",
            0,
            vec![(Whitespace, 6..7), (Error, 7..8), (Error, 8..11)],
        ),
        ("cast(x @\r\n", 0, vec![(Whitespace, 6..7), (Error, 7..8)]),
        (
            "cast(x @ ] tail",
            0,
            vec![(Whitespace, 6..7), (Error, 7..8)],
        ),
        (
            "cast(x @ else tail",
            STOP_ELSE,
            vec![(Whitespace, 6..7), (Error, 7..8)],
        ),
        (
            "cast(x @ ): T;",
            0,
            vec![
                (Whitespace, 6..7),
                (Error, 7..8),
                (Whitespace, 8..9),
                (RParen, 9..10),
            ],
        ),
        (
            "cast(x @ : T;",
            0,
            vec![(Whitespace, 6..7), (Error, 7..8), (Whitespace, 8..9)],
        ),
        (
            "cast(x @ ;",
            0,
            vec![(Whitespace, 6..7), (Error, 7..8), (Whitespace, 8..9)],
        ),
        (
            "cast(x @ = value",
            0,
            vec![(Whitespace, 6..7), (Error, 7..8), (Whitespace, 8..9)],
        ),
        (
            "cast(x @ 💥 ): T;",
            0,
            vec![
                (Whitespace, 6..7),
                (Error, 7..8),
                (Error, 8..9),
                (Error, 9..13),
                (Whitespace, 13..14),
                (RParen, 14..15),
            ],
        ),
    ] {
        let (green, _, _) = run_cast_declaration(source, stops, 0, LineEntry::InLine, None);
        let node = declaration(&green);
        let pattern = node
            .children()
            .find(|child| child.kind() == SyntaxKind::CastPattern)
            .unwrap();
        assert_eq!(pattern.parent(), Some(node.clone()));
        let actual = pattern
            .children_with_tokens()
            .map(|child| {
                match child.kind() {
                    Missing | Pattern => assert!(child.as_node().is_some()),
                    _ => assert!(child.as_token().is_some()),
                }
                let range = child.text_range();
                (
                    child.kind(),
                    usize::from(range.start())..usize::from(range.end()),
                )
            })
            .collect::<Vec<_>>();
        let mut expected = vec![(LParen, 4..5), (Pattern, 5..6)];
        expected.extend(terminal);
        assert_eq!(actual, expected, "{source:?}");
        assert!(
            !node
                .descendants_with_tokens()
                .any(|child| child.kind() == SyntaxKind::Invalid),
            "{source:?}"
        );
    }
}

#[test]
fn cast_pattern_close_direct_rowan_phase_and_boundary_ownership() {
    use SyntaxKind::{CastKw, CastPattern, CastTarget, Colon, Equals, Semicolon};

    for prefix in ["cast(x", "cast(x @"] {
        for (suffix, owner, punctuation) in [
            (": T;", CastTarget, Colon),
            (";", Semicolon, Semicolon),
            ("= value", Equals, Equals),
        ] {
            // Immediate colon is Pattern annotation; only the malformed
            // close run reaches the Cast target-introducer retry here.
            if prefix == "cast(x" && punctuation == Colon {
                continue;
            }
            let source = format!("{prefix} {suffix}");
            let (green, _, _) = run_cast_declaration(&source, 0, 0, LineEntry::InLine, None);
            let node = declaration(&green);
            let mut children = node.children_with_tokens();
            assert_eq!(children.next().unwrap().kind(), CastKw);
            assert_eq!(children.next().unwrap().kind(), CastPattern);
            let next = children.next().expect("next phase retains punctuation");
            assert_eq!(next.kind(), owner, "{source:?}");
            let token = match next {
                rowan::NodeOrToken::Node(node) => node.first_token().unwrap(),
                rowan::NodeOrToken::Token(token) => token,
            };
            assert_eq!(token.kind(), punctuation);
            assert_eq!(usize::from(token.text_range().start()), prefix.len() + 1);
            assert_eq!(usize::from(token.text_range().end()), prefix.len() + 2);
        }
        for (suffix, stops) in [
            (" ] tail", 0),
            (" } tail", 0),
            (" else tail", STOP_ELSE),
            ("\r\n", 0),
        ] {
            let source = format!("{prefix}{suffix}");
            let (green, _, _) = run_cast_declaration(&source, stops, 0, LineEntry::InLine, None);
            let node = declaration(&green);
            assert_eq!(
                node.children_with_tokens()
                    .map(|child| child.kind())
                    .collect::<Vec<_>>(),
                [CastKw, CastPattern],
                "{source:?}"
            );
            assert_eq!(
                usize::from(node.text_range().end()),
                prefix.len(),
                "{source:?}"
            );
        }
    }
}

#[test]
fn cast_nested_ml_application_keeps_else_after_the_synthesized_outer_close() {
    let source = "cast((f x) else tail";
    let (green, exit, remainder) =
        run_cast_declaration(source, STOP_ELSE, 0, LineEntry::InLine, None);
    let node = declaration(&green);
    assert_eq!(
        node.descendants()
            .filter(|child| child.kind() == SyntaxKind::PatternMlApplicationTail)
            .count(),
        1
    );
    assert_eq!(usize::from(node.text_range().end()), "cast((f x)".len());
    assert_eq!(remainder, " tail");
    let cast_pattern = node
        .children()
        .find(|child| child.kind() == SyntaxKind::CastPattern)
        .expect("CastPattern");
    assert_eq!(
        cast_pattern
            .children_with_tokens()
            .map(|child| child.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::LParen, SyntaxKind::Pattern, SyntaxKind::Missing,]
    );
    assert_eq!(count(&node, SyntaxKind::Missing), 1);
    assert_eq!(count(&node, SyntaxKind::Error), 0);
    assert!(
        !node
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.text() == "else")
    );
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().spelling(), Some("else"));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");
}

#[test]
fn cast_direct_pattern_stop_else_keeps_the_outer_item_pending() {
    let source = "cast(x else tail";
    let (green, exit, facts, remainder) = typed_cast(source, 0, STOP_ELSE, None);
    assert_eq!(green.to_string(), "cast(x");
    assert_eq!(remainder, " tail");
    assert_eq!(facts, [structural_fact(StructuralKind::Missing, 6..6)]);
    let node = declaration(&green);
    let cast_pattern = node
        .children()
        .find(|child| child.kind() == SyntaxKind::CastPattern)
        .expect("CastPattern");
    assert_eq!(usize::from(cast_pattern.text_range().end()), 6);
    assert_eq!(
        cast_pattern
            .children_with_tokens()
            .map(|child| child.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::LParen, SyntaxKind::Pattern, SyntaxKind::Missing]
    );
    assert_eq!(count(&node, SyntaxKind::PatternMlApplicationTail), 0);
    assert!(
        !node
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.text() == "else")
    );
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().spelling(), Some("else"));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");
}

#[test]
fn cast_pattern_close_exact_equals_preserves_form_and_body() {
    for malformed in ["@", "@ ==", "@ =>", "@ =>>"] {
        for body in ["", " value"] {
            let prefix = format!("cast(x {malformed}");
            let source = format!("{prefix} ={body}");
            let (green, _, _) = run_cast_declaration(&source, 0, 0, LineEntry::InLine, None);
            let node = declaration(&green);
            let children = node.children_with_tokens().collect::<Vec<_>>();
            assert_eq!(children[1].kind(), SyntaxKind::CastPattern, "{source:?}");
            let pattern = children[1].as_node().unwrap();
            assert_eq!(usize::from(pattern.text_range().end()), prefix.len() + 1);
            let errors = pattern
                .children_with_tokens()
                .filter(|child| child.kind() == SyntaxKind::Error)
                .collect::<Vec<_>>();
            assert_eq!(usize::from(errors.first().unwrap().text_range().start()), 7);
            assert_eq!(
                usize::from(errors.last().unwrap().text_range().end()),
                prefix.len()
            );
            assert_eq!(pattern.last_token().unwrap().kind(), SyntaxKind::Whitespace);
            assert!(
                !pattern
                    .descendants()
                    .any(|child| child.kind() == SyntaxKind::Missing)
            );
            assert_eq!(children[2].kind(), SyntaxKind::Equals, "{source:?}");
            assert_eq!(children[2].as_token().unwrap().text(), "=");
            assert_eq!(
                usize::from(children[2].text_range().start()),
                prefix.len() + 1
            );
            assert_eq!(children.len(), 4, "{source:?}");
            assert_eq!(children[3].kind(), SyntaxKind::CastBody, "{source:?}");
            let statement = children[3].as_node().unwrap();
            assert_eq!(statement.to_string(), body);
            assert_eq!(
                statement
                    .descendants()
                    .any(|child| child.kind() == SyntaxKind::Missing),
                body.is_empty()
            );
        }
    }
}

#[test]
fn cast_pattern_absence_structural_facts_are_exact() {
    for origin in [100, 12_000] {
        for source in [
            "cast(",
            "cast(\r\n",
            "cast()",
            "cast(: T;",
            "cast(;",
            "cast(= value",
        ] {
            let mut expected = vec![structural_fact(StructuralKind::Missing, 5..5)];
            if source == "cast()" {
                expected.push(structural_fact(StructuralKind::Missing, 6..6));
            }
            let (_, _, facts, _) = typed_cast(source, origin, 0, None);
            assert_eq!(facts, expected, "{source:?} at {origin}");
        }
    }
}

#[test]
fn cast_pattern_value_direct_rowan_absence_order_and_phase_handoff() {
    use SyntaxKind::{CastPattern, CastTarget, Colon, Equals, LParen, Missing, RParen, Semicolon};

    // A native opener selects the required value slot. Its Missing precedes
    // either the native local close or the next phase outside CastPattern.
    for (source, close, phase) in [
        ("cast()", true, None),
        ("cast(: T;", false, Some((CastTarget, Colon))),
        ("cast(;", false, Some((Semicolon, Semicolon))),
        ("cast(= value", false, Some((Equals, Equals))),
    ] {
        let (green, _, _) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        let node = declaration(&green);
        let mut children = node.children_with_tokens();
        let pattern = children
            .by_ref()
            .find(|child| child.kind() == CastPattern)
            .unwrap()
            .into_node()
            .unwrap();
        assert_eq!(pattern.parent(), Some(node.clone()), "{source:?}");
        let actual = pattern
            .children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    usize::from(range.start())..usize::from(range.end()),
                )
            })
            .collect::<Vec<_>>();
        let mut expected = vec![(LParen, 4..5), (Missing, 5..5)];
        if close {
            expected.push((RParen, 5..6));
        }
        assert_eq!(actual, expected, "{source:?}");
        if let Some((owner, punctuation)) = phase {
            let next = children.next().expect("preserved next phase");
            assert_eq!(next.kind(), owner, "{source:?}");
            let token = match next {
                rowan::NodeOrToken::Node(node) => node.first_token().unwrap(),
                rowan::NodeOrToken::Token(token) => token,
            };
            assert_eq!(token.kind(), punctuation, "{source:?}");
            assert_eq!(
                token.text_range(),
                rowan::TextRange::new(5.into(), 6.into()),
                "{source:?}"
            );
        }
    }
}

#[test]
fn cast_pattern_value_direct_rowan_boundary_has_no_later_slot() {
    use SyntaxKind::{CastKw, CastPattern, LParen, Missing};

    for (source, stops) in [
        ("cast(", 0),
        ("cast(\r\n", 0),
        ("cast( else tail", STOP_ELSE),
        ("cast( } tail", 0),
    ] {
        let (green, _, _) = run_cast_declaration(source, stops, 0, LineEntry::InLine, None);
        let node = declaration(&green);
        assert_eq!(
            node.children_with_tokens()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            [CastKw, CastPattern],
            "{source:?}"
        );
        let pattern = node.children().next().unwrap();
        let actual = pattern
            .children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    usize::from(range.start())..usize::from(range.end()),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(actual, [(LParen, 4..5), (Missing, 5..5)], "{source:?}");
    }
}

#[test]
fn cast_pattern_initial_shared_slots_have_direct_rowan_selectors() {
    use SyntaxKind::*;

    for (source, pattern_end, initial_children, tail_children, expected_recoveries) in [
        (
            "cast(|x): T;",
            7,
            vec![(Missing, 5..5), (PatternAlternationTail, 5..7)],
            vec![(Pipe, 5..6), (Pattern, 6..7)],
            vec![structural_fact(StructuralKind::Missing, 5..5)],
        ),
        (
            "cast(@ x): T;",
            8,
            vec![(Error, 5..6), (Whitespace, 6..7), (IdentifierPattern, 7..8)],
            vec![],
            vec![structural_fact(StructuralKind::ErrorGroup, 5..6)],
        ),
        (
            "cast(|): T;",
            6,
            vec![(Missing, 5..5), (PatternAlternationTail, 5..6)],
            vec![(Pipe, 5..6), (Pattern, 6..6)],
            vec![
                structural_fact(StructuralKind::Missing, 5..5),
                structural_fact(StructuralKind::Missing, 6..6),
            ],
        ),
    ] {
        let (green, exit, remainder) = run_statement_normalized(source, 0, LineEntry::InLine, None);
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.kind(), Root);
        assert_eq!(root.parent(), None);
        assert_eq!(root.text().to_string(), source);
        assert_eq!(
            root.text_range(),
            rowan::TextRange::new(0.into(), (source.len() as u32).into())
        );
        let exact = |node: &SyntaxNode, expected: &[(SyntaxKind, std::ops::Range<usize>)]| {
            let children = node.children_with_tokens().collect::<Vec<_>>();
            assert_eq!(children.len(), expected.len(), "{source}: {node:?}");
            for (child, (kind, range)) in children.iter().zip(expected) {
                assert_eq!(child.kind(), *kind);
                assert_eq!(child.parent().as_ref(), Some(node));
                assert_eq!(
                    child.as_node().is_some(),
                    matches!(
                        kind,
                        Statement
                            | CastDeclaration
                            | CastPattern
                            | CastTarget
                            | Pattern
                            | PatternAlternationTail
                            | IdentifierPattern
                            | TypeExpression
                            | Missing
                    )
                );
                assert_eq!(
                    child.text_range(),
                    rowan::TextRange::new((range.start as u32).into(), (range.end as u32).into())
                );
                assert_eq!(child.to_string(), &source[range.clone()]);
            }
        };
        exact(&root, &[(Statement, 0..source.len())]);
        let statement = root.first_child().unwrap();
        exact(&statement, &[(CastDeclaration, 0..source.len())]);
        let cast = statement.first_child().unwrap();
        exact(
            &cast,
            &[
                (CastKw, 0..4),
                (CastPattern, 4..pattern_end + 1),
                (CastTarget, pattern_end + 1..pattern_end + 4),
                (Semicolon, pattern_end + 4..pattern_end + 5),
            ],
        );
        let cast_pattern = cast.first_child().unwrap();
        exact(
            &cast_pattern,
            &[
                (LParen, 4..5),
                (Pattern, 5..pattern_end),
                (RParen, pattern_end..pattern_end + 1),
            ],
        );
        let pattern = cast_pattern.first_child().unwrap();
        exact(&pattern, &initial_children);
        if let Some(tail) = pattern
            .children()
            .find(|node| node.kind() == PatternAlternationTail)
        {
            exact(&tail, &tail_children);
            let rhs = tail.first_child().unwrap();
            if rhs.text_range().is_empty() {
                exact(&rhs, &[(Missing, 6..6)]);
            } else {
                exact(&rhs, &[(IdentifierPattern, 6..7)]);
                exact(&rhs.first_child().unwrap(), &[(Identifier, 6..7)]);
                assert!(
                    !rhs.descendants_with_tokens()
                        .any(|element| matches!(element.kind(), Missing | Error | Invalid))
                );
            }
        } else {
            exact(&pattern.first_child().unwrap(), &[(Identifier, 7..8)]);
        }
        let target = cast.children().nth(1).unwrap();
        exact(
            &target,
            &[
                (Colon, pattern_end + 1..pattern_end + 2),
                (Whitespace, pattern_end + 2..pattern_end + 3),
                (TypeExpression, pattern_end + 3..pattern_end + 4),
            ],
        );

        // Direct Rowan ancestry and child position distinguish the two Missing
        // nodes without parser-owned recovery state.
        let projected = root
            .descendants_with_tokens()
            .filter(|element| matches!(element.kind(), Missing | Error | Invalid))
            .map(|element| {
                let owner = element.parent().unwrap();
                assert_eq!(owner.kind(), Pattern);
                assert_eq!(owner.first_child_or_token().as_ref(), Some(&element));
                match element.kind() {
                    Missing => assert!(
                        element
                            .as_node()
                            .unwrap()
                            .children_with_tokens()
                            .next()
                            .is_none()
                    ),
                    Error => {
                        assert!(element.as_token().is_some());
                        assert_eq!(element.next_sibling_or_token().unwrap().kind(), Whitespace);
                    }
                    _ => panic!("unexpected recovery category"),
                }
                match owner.parent().unwrap().kind() {
                    CastPattern => {
                        assert_eq!(owner.parent(), Some(cast_pattern.clone()));
                    }
                    PatternAlternationTail => {
                        let parent = owner.parent().unwrap();
                        assert_eq!(parent.parent().as_ref(), Some(&pattern));
                        assert_eq!(parent.first_child_or_token().unwrap().kind(), Pipe);
                        assert_eq!(
                            parent.last_child_or_token().unwrap().as_node(),
                            Some(&owner)
                        );
                    }
                    _ => panic!("unexpected initial Pattern owner"),
                }
                let range = element.text_range();
                (
                    match element.kind() {
                        Missing => StructuralKind::Missing,
                        Error => StructuralKind::ErrorGroup,
                        _ => unreachable!(),
                    },
                    usize::from(range.start())..usize::from(range.end()),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(projected, expected_recoveries, "{source}");
        assert_eq!(remainder, "");
        let NormalizedExit::Complete(Err(Either::Right(end)), LineEntry::InLine) = exit else {
            panic!("bodyless Cast must return the EOF Item in-line")
        };
        let mut item = end.item;
        assert!(item.payload_view().is_eof());
        assert_eq!(emit_pending_leading_text(&mut item), "");
    }
}

#[test]
fn cast_pattern_value_direct_rowan_nonempty_error_keeps_pattern_owner() {
    use SyntaxKind::{CastPattern, Error, LParen, Pattern, RParen};

    let (green, _, _) = run_cast_declaration("cast(@): T;", 0, 0, LineEntry::InLine, None);
    let node = declaration(&green);
    let pattern = node
        .children()
        .find(|child| child.kind() == CastPattern)
        .unwrap();
    let children = pattern.children_with_tokens().collect::<Vec<_>>();
    let actual = children
        .iter()
        .map(|child| {
            let range = child.text_range();
            (
                child.kind(),
                usize::from(range.start())..usize::from(range.end()),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(actual, [(LParen, 4..5), (Pattern, 5..6), (RParen, 6..7)]);
    let value = children[1].as_node().unwrap();
    assert_eq!(value.parent(), Some(pattern));
    let mut errors = value
        .descendants_with_tokens()
        .filter(|child| child.kind() == Error);
    let error = errors.next().expect("native Pattern Error token");
    assert!(error.as_token().is_some());
    assert_eq!(
        error.text_range(),
        rowan::TextRange::new(5.into(), 6.into())
    );
    assert!(errors.next().is_none());
}

#[test]
fn cast_pattern_introducer_direct_rowan_slot_order_and_ranges() {
    use SyntaxKind::{CastKw, CastPattern, Error, Missing, Whitespace};

    // Stop at the first grammar child: its value/close and later phases have
    // separate owners. Only immediate children identify this bounded slot.
    for (source, stops, expected) in [
        ("cast", 0, vec![(CastKw, 0..4), (Missing, 4..4)]),
        ("cast )", 0, vec![(CastKw, 0..4), (Missing, 4..4)]),
        (
            "cast else tail",
            STOP_ELSE,
            vec![(CastKw, 0..4), (Missing, 4..4)],
        ),
        (
            "cast @",
            0,
            vec![(CastKw, 0..4), (Whitespace, 4..5), (Error, 5..6)],
        ),
        (
            "cast @   ",
            0,
            vec![
                (CastKw, 0..4),
                (Whitespace, 4..5),
                (Error, 5..6),
                (Error, 6..9),
            ],
        ),
        (
            "cast @\r\n",
            0,
            vec![(CastKw, 0..4), (Whitespace, 4..5), (Error, 5..6)],
        ),
        (
            "cast @ )",
            0,
            vec![(CastKw, 0..4), (Whitespace, 4..5), (Error, 5..6)],
        ),
        (
            "cast @ else tail",
            STOP_ELSE,
            vec![(CastKw, 0..4), (Whitespace, 4..5), (Error, 5..6)],
        ),
        (
            "cast @ x",
            0,
            vec![
                (CastKw, 0..4),
                (Whitespace, 4..5),
                (Error, 5..6),
                (Whitespace, 6..7),
                (CastPattern, 7..8),
            ],
        ),
        (
            "cast @ (x): T;",
            0,
            vec![
                (CastKw, 0..4),
                (Whitespace, 4..5),
                (Error, 5..6),
                (Whitespace, 6..7),
                (CastPattern, 7..10),
            ],
        ),
        ("cast(x): T;", 0, vec![(CastKw, 0..4), (CastPattern, 4..7)]),
        (
            "cast x",
            0,
            vec![(CastKw, 0..4), (Whitespace, 4..5), (CastPattern, 5..6)],
        ),
    ] {
        let (green, _, _) = run_cast_declaration(source, stops, 0, LineEntry::InLine, None);
        let node = declaration(&green);
        let mut actual = Vec::new();
        for child in node.children_with_tokens() {
            let kind = child.kind();
            let range = child.text_range();
            actual.push((kind, usize::from(range.start())..usize::from(range.end())));
            if kind == CastPattern {
                break;
            }
        }
        assert_eq!(actual, expected, "{source:?}");
        assert!(
            node.children()
                .all(|child| child.kind() != SyntaxKind::Invalid),
            "{source:?}"
        );
    }
}

#[test]
fn cast_pattern_introducer_initial_pattern_children_distinguish_value_recovery() {
    use SyntaxKind::{CastPattern, LParen, Missing, Pattern, RParen};

    for (source, expected) in [
        ("cast x", vec![(Missing, 5..5), (Pattern, 5..6)]),
        (
            "cast(x): T;",
            vec![(LParen, 4..5), (Pattern, 5..6), (RParen, 6..7)],
        ),
        // The outer Error and native retry leading are witnessed above.
        // Bare-Pattern retry starts with its value, without a second opener Missing.
        ("cast @ x", vec![(Pattern, 7..8)]),
        // This Missing follows the native opener: it belongs to the value slot,
        // not the PatternIntroducer, despite having the same CastPattern parent.
        (
            "cast(): T;",
            vec![(LParen, 4..5), (Missing, 5..5), (RParen, 5..6)],
        ),
    ] {
        let (green, _, _) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        let node = declaration(&green);
        let pattern = node
            .children()
            .find(|child| child.kind() == CastPattern)
            .expect("initial direct CastPattern");
        assert_eq!(pattern.parent(), Some(node), "{source:?}");
        let actual = pattern
            .children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    usize::from(range.start())..usize::from(range.end()),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(actual, expected, "{source:?}");
    }
}

#[test]
fn cast_pattern_introducer_rowan_error_group_ends_before_phase_handoff() {
    use SyntaxKind::{CastKw, CastTarget, Colon, Equals, Error, Semicolon, Whitespace};

    for (source, handoff, punctuation) in [
        ("cast @ : T;", CastTarget, Colon),
        ("cast @ = x", Equals, Equals),
        ("cast @ ;", Semicolon, Semicolon),
    ] {
        let (green, _, _) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        let node = declaration(&green);
        let mut children = node.children_with_tokens();
        let prefix = children
            .by_ref()
            .take(4)
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    usize::from(range.start())..usize::from(range.end()),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            prefix,
            [
                (CastKw, 0..4),
                (Whitespace, 4..5),
                (Error, 5..6),
                (Whitespace, 6..7)
            ],
            "{source:?}"
        );
        let next = children.next().expect("native phase handoff");
        assert_eq!(next.kind(), handoff, "{source:?}");
        let token = match next {
            rowan::NodeOrToken::Node(node) => node.first_token().expect("target punctuation"),
            rowan::NodeOrToken::Token(token) => token,
        };
        assert_eq!(token.kind(), punctuation, "{source:?}");
        assert_eq!(
            usize::from(token.text_range().start())..usize::from(token.text_range().end()),
            7..8,
            "{source:?}"
        );
    }
}

#[test]
fn cast_pattern_introducer_structural_facts_are_exact_and_shifted() {
    for origin in [100, 12_000] {
        for (source, stops, kind, relative_range) in [
            ("cast", 0, StructuralKind::Missing, 4..4),
            ("cast x", 0, StructuralKind::Missing, 5..5),
            ("cast;", 0, StructuralKind::Missing, 4..4),
            ("cast: T;", 0, StructuralKind::Missing, 4..4),
            ("cast= x", 0, StructuralKind::Missing, 4..4),
            ("cast )", 0, StructuralKind::Missing, 4..4),
            ("cast else tail", STOP_ELSE, StructuralKind::Missing, 4..4),
            ("cast @", 0, StructuralKind::ErrorGroup, 5..6),
            ("cast @ x", 0, StructuralKind::ErrorGroup, 5..6),
            ("cast @ # x", 0, StructuralKind::ErrorGroup, 5..8),
            ("cast @ (x): T;", 0, StructuralKind::ErrorGroup, 5..6),
            ("cast @ : T;", 0, StructuralKind::ErrorGroup, 5..6),
            ("cast @ = x", 0, StructuralKind::ErrorGroup, 5..6),
            ("cast @ )", 0, StructuralKind::ErrorGroup, 5..6),
            ("cast @   ", 0, StructuralKind::ErrorGroup, 5..9),
            ("cast @\r\n", 0, StructuralKind::ErrorGroup, 5..6),
            ("cast @ あ x", 0, StructuralKind::ErrorGroup, 5..6),
        ] {
            let mut expected = vec![structural_fact(kind, relative_range)];
            if source == "cast @ あ x" {
                expected.push(structural_fact(StructuralKind::Missing, 11..11));
                expected.push(structural_fact(StructuralKind::Missing, 12..12));
            }
            let (_, _, facts, _) = typed_cast(source, origin, stops, None);
            assert_eq!(facts, expected, "{source:?} at {origin}");
        }
    }
}

#[test]
fn cast_private_owner_builds_bodyless_inline_and_indented_forms() {
    for (source, body, indented) in [
        ("cast(x: A): B;", 0, 0),
        ("pub cast(x: A): B = x", 1, 0),
        ("cast(x: A): B =\n  x", 1, 1),
    ] {
        let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::CastPattern),
            1,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::CastTarget), 1, "{source:?}");
        assert_eq!(
            count(&declaration, SyntaxKind::CastBody),
            body,
            "{source:?}"
        );
        assert_eq!(
            count(&declaration, SyntaxKind::IndentedStatementBlock),
            indented,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
        if source == "cast(x: A): B;" {
            let cast_pattern = declaration
                .children()
                .find(|child| child.kind() == SyntaxKind::CastPattern)
                .expect("CastPattern");
            let pattern = cast_pattern
                .children()
                .find(|child| child.kind() == SyntaxKind::Pattern)
                .expect("direct Pattern");
            assert_eq!(
                pattern
                    .children()
                    .map(|child| child.kind())
                    .collect::<Vec<_>>(),
                [
                    SyntaxKind::IdentifierPattern,
                    SyntaxKind::PatternTypeAnnotation,
                ]
            );
            assert_eq!(
                declaration
                    .children()
                    .find(|child| child.kind() == SyntaxKind::CastTarget)
                    .expect("CastTarget")
                    .to_string(),
                ": B"
            );
        }
    }

    let source = "pub cast(x: int): user_id = user_id { raw: x }";
    let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::CastBody), 1);
    assert!(count(&declaration, SyntaxKind::OperatorChain) >= 1);
    assert_eq!(
        count(&declaration, SyntaxKind::BracedStatementBlockExpression),
        1
    );
    assert_eq!(count(&declaration, SyntaxKind::Missing), 0);
    assert_eq!(count(&declaration, SyntaxKind::Error), 0);
    assert_eq!(
        declaration
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::PubKw,
            SyntaxKind::Whitespace,
            SyntaxKind::CastKw,
            SyntaxKind::CastPattern,
            SyntaxKind::CastTarget,
            SyntaxKind::Whitespace,
            SyntaxKind::Equals,
            SyntaxKind::CastBody,
        ]
    );
}

fn assert_cast_children(node: &SyntaxNode, expected: &[(SyntaxKind, std::ops::Range<usize>)]) {
    let actual = node
        .children_with_tokens()
        .map(|child| {
            match child.kind() {
                SyntaxKind::CastDeclaration
                | SyntaxKind::CastPattern
                | SyntaxKind::CastTarget
                | SyntaxKind::CastBody
                | SyntaxKind::Pattern
                | SyntaxKind::TypeExpression
                | SyntaxKind::OperatorChain
                | SyntaxKind::IndentedStatementBlock
                | SyntaxKind::Statement
                | SyntaxKind::MlArgument
                | SyntaxKind::BracedStatementBlockExpression
                | SyntaxKind::IdentifierExpression => {
                    assert_eq!(child.as_node().unwrap().parent().as_ref(), Some(node));
                }
                _ => assert_eq!(child.as_token().unwrap().parent().as_ref(), Some(node)),
            }
            let range = child.text_range();
            (
                child.kind(),
                usize::from(range.start())..usize::from(range.end()),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(actual, expected, "{node:?}");
}

#[test]
fn cast_declaration_direct_rowan_accepted_composition() {
    use SyntaxKind::*;
    for (source, expected, body_children) in [
        (
            "cast(x: A): B;",
            vec![
                (CastKw, 0..4),
                (CastPattern, 4..10),
                (CastTarget, 10..13),
                (Semicolon, 13..14),
            ],
            vec![],
        ),
        (
            "pub cast(x: A): B = x",
            vec![
                (PubKw, 0..3),
                (Whitespace, 3..4),
                (CastKw, 4..8),
                (CastPattern, 8..14),
                (CastTarget, 14..17),
                (Whitespace, 17..18),
                (Equals, 18..19),
                (CastBody, 19..21),
            ],
            vec![(Whitespace, 19..20), (OperatorChain, 20..21)],
        ),
        (
            "cast(x: A): B =\n  x",
            vec![
                (CastKw, 0..4),
                (CastPattern, 4..10),
                (CastTarget, 10..13),
                (Whitespace, 13..14),
                (Equals, 14..15),
                (CastBody, 15..19),
            ],
            vec![(IndentedStatementBlock, 15..19)],
        ),
        (
            "pub cast(x: int): user_id = user_id { raw: x }",
            vec![
                (PubKw, 0..3),
                (Whitespace, 3..4),
                (CastKw, 4..8),
                (CastPattern, 8..16),
                (CastTarget, 16..25),
                (Whitespace, 25..26),
                (Equals, 26..27),
                (CastBody, 27..46),
            ],
            vec![(Whitespace, 27..28), (OperatorChain, 28..46)],
        ),
    ] {
        let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some());
        assert_eq!(remainder, "");
        assert_eq!(green.to_string(), source);
        let node = declaration(&green);
        assert_cast_children(&node, &expected);
        for (kind, range) in &expected {
            if *kind == CastPattern || *kind == CastTarget {
                let child = node.children().find(|child| child.kind() == *kind).unwrap();
                let start = range.start;
                let end = range.end;
                let children = if *kind == CastPattern {
                    vec![
                        (LParen, start..start + 1),
                        (Pattern, start + 1..end - 1),
                        (RParen, end - 1..end),
                    ]
                } else {
                    vec![
                        (Colon, start..start + 1),
                        (Whitespace, start + 1..start + 2),
                        (TypeExpression, start + 2..end),
                    ]
                };
                assert_cast_children(&child, &children);
            }
        }
        assert!(
            !node
                .descendants_with_tokens()
                .any(|child| matches!(child.kind(), Missing | Error | Invalid))
        );
        if let Some(body) = node.children().find(|child| child.kind() == CastBody) {
            assert_cast_children(&body, &body_children);
            if let Some(block) = body
                .children()
                .find(|child| child.kind() == IndentedStatementBlock)
            {
                assert_cast_children(
                    &block,
                    &[(Newline, 15..16), (Whitespace, 16..18), (Statement, 18..19)],
                );
            }
            if source.contains('{') {
                let expression = body.children().next().unwrap();
                assert_cast_children(
                    &expression,
                    &[
                        (IdentifierExpression, 28..35),
                        (Whitespace, 35..36),
                        (MlArgument, 36..46),
                    ],
                );
                let argument = expression.children().last().unwrap();
                assert_cast_children(&argument, &[(OperatorChain, 36..46)]);
                let argument_expression = argument.children().next().unwrap();
                assert_cast_children(
                    &argument_expression,
                    &[(BracedStatementBlockExpression, 36..46)],
                );
            }
        }
    }
}

#[test]
fn cast_declaration_direct_rowan_error_retry_composition() {
    use SyntaxKind::*;
    // Each full declaration locates recovery by ordered CST phase, including
    // the Pattern-owned nonempty value error. No ledger or Error text selects it.
    for (source, expected, owner_kind, owner_children) in [
        (
            "cast @ (x): T;",
            vec![
                (CastKw, 0..4),
                (Whitespace, 4..5),
                (Error, 5..6),
                (Whitespace, 6..7),
                (CastPattern, 7..10),
                (CastTarget, 10..13),
                (Semicolon, 13..14),
            ],
            CastDeclaration,
            vec![],
        ),
        (
            "cast(@): T;",
            vec![
                (CastKw, 0..4),
                (CastPattern, 4..7),
                (CastTarget, 7..10),
                (Semicolon, 10..11),
            ],
            Pattern,
            vec![(Error, 5..6)],
        ),
        (
            "cast(x @ ): T;",
            vec![
                (CastKw, 0..4),
                (CastPattern, 4..10),
                (CastTarget, 10..13),
                (Semicolon, 13..14),
            ],
            CastPattern,
            vec![
                (LParen, 4..5),
                (Pattern, 5..6),
                (Whitespace, 6..7),
                (Error, 7..8),
                (Whitespace, 8..9),
                (RParen, 9..10),
            ],
        ),
        (
            "cast(x) @ : T;",
            vec![
                (CastKw, 0..4),
                (CastPattern, 4..7),
                (Whitespace, 7..8),
                (Error, 8..9),
                (Whitespace, 9..10),
                (CastTarget, 10..13),
                (Semicolon, 13..14),
            ],
            CastDeclaration,
            vec![],
        ),
        (
            "cast(x): T @ ;",
            vec![
                (CastKw, 0..4),
                (CastPattern, 4..7),
                (CastTarget, 7..10),
                (Whitespace, 10..11),
                (Error, 11..12),
                (Whitespace, 12..13),
                (Semicolon, 13..14),
            ],
            CastDeclaration,
            vec![],
        ),
        (
            "cast(x): T @ = value",
            vec![
                (CastKw, 0..4),
                (CastPattern, 4..7),
                (CastTarget, 7..10),
                (Whitespace, 10..11),
                (Error, 11..12),
                (Whitespace, 12..13),
                (Equals, 13..14),
                (CastBody, 14..20),
            ],
            CastDeclaration,
            vec![],
        ),
        (
            "cast(x): T = @ value",
            vec![
                (CastKw, 0..4),
                (CastPattern, 4..7),
                (CastTarget, 7..10),
                (Whitespace, 10..11),
                (Equals, 11..12),
                (CastBody, 12..20),
            ],
            CastBody,
            vec![
                (Whitespace, 12..13),
                (Error, 13..14),
                (Whitespace, 14..15),
                (OperatorChain, 15..20),
            ],
        ),
    ] {
        let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some());
        assert_eq!(remainder, "");
        assert_eq!(green.to_string(), source);
        let node = declaration(&green);
        assert_cast_children(&node, &expected);
        let owner = node
            .descendants()
            .find(|child| child.kind() == owner_kind)
            .unwrap();
        if owner_kind != CastDeclaration {
            assert_cast_children(&owner, &owner_children);
        }
        let errors = node
            .descendants_with_tokens()
            .filter(|child| child.kind() == Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{source}");
        assert_eq!(errors[0].as_token().unwrap().parent(), Some(owner));
        assert!(
            !node
                .descendants()
                .any(|child| matches!(child.kind(), Missing | Invalid))
        );
    }
}

#[test]
fn cast_intro_is_exact_visibility_aware_and_uses_canonical_statement_dispatch() {
    for source in [
        "cast(x): T;",
        "my cast(x): T;",
        "our cast (x): T;",
        "pub cast(x): T;",
        "pub\n  cast\n    (x): T;",
    ] {
        let (green, exit, _) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(token_count(&declaration(&green), SyntaxKind::CastKw), 1);
    }

    for source in [
        "casting(x): T;",
        "castaway(x): T;",
        "mycast(x): T;",
        "my castish(x): T;",
        "our\ncast(x): T;",
        "\ncast(x): T;",
    ] {
        let (green, exit, remainder) =
            run_cast_declaration(source, 0, 700, LineEntry::InLine, None);
        assert!(exit.is_none(), "{source:?}");
        assert_eq!(green.to_string(), "", "{source:?}");
        assert_eq!(remainder, source, "{source:?}");
    }

    let source = "my cast = value";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert!(exit.is_some());
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);
    assert_eq!(count(&declaration, SyntaxKind::BindingStatement), 0);
    assert_eq!(count(&declaration, SyntaxKind::CastBody), 1);

    let (green, _) = run_statement("cast(x): T;");
    assert_eq!(green.to_string(), "cast(x): T;");
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::CastDeclaration)
            .count(),
        1
    );
}

#[test]
fn cast_normal_braced_statement_dispatch_has_direct_rowan_ownership() {
    use SyntaxKind::*;

    let source = "{ cast(x): T; }";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.kind(), Root);
    assert_eq!(
        root.text_range(),
        rowan::TextRange::new(0.into(), 15.into())
    );
    assert_cast_children(&root, &[(Statement, 0..15)]);
    let outer_statement = root.first_child().unwrap();
    assert_cast_children(&outer_statement, &[(OperatorChain, 0..15)]);
    let expression = outer_statement.first_child().unwrap();
    assert_cast_children(&expression, &[(BracedStatementBlockExpression, 0..15)]);
    let block = expression.first_child().unwrap();
    assert_cast_children(
        &block,
        &[
            (LBrace, 0..1),
            (Whitespace, 1..2),
            (Statement, 2..13),
            (Whitespace, 13..14),
            (RBrace, 14..15),
        ],
    );
    let statement = block.first_child().unwrap();
    assert_cast_children(&statement, &[(CastDeclaration, 2..13)]);
    let declaration = statement.first_child().unwrap();
    assert_cast_children(
        &declaration,
        &[
            (CastKw, 2..6),
            (CastPattern, 6..9),
            (CastTarget, 9..12),
            (Semicolon, 12..13),
        ],
    );
    let pattern = declaration.first_child().unwrap();
    assert_cast_children(&pattern, &[(LParen, 6..7), (Pattern, 7..8), (RParen, 8..9)]);
    let target = pattern.next_sibling().unwrap();
    assert_cast_children(
        &target,
        &[
            (Colon, 9..10),
            (Whitespace, 10..11),
            (TypeExpression, 11..12),
        ],
    );
    assert!(!root.descendants_with_tokens().any(|element| matches!(
        element.kind(),
        Missing | Error | Invalid | CastBody | MlArgument | IndentedStatementBlock
    )));
}

#[test]
fn cast_pattern_reuses_full_pattern_surface_and_nested_close_handoffs() {
    for source in [
        "cast(:symbol): T;",
        "cast(x: Source): Target;",
        "cast({x = 1}): T;",
        "cast([x, ..rest]): T;",
        "cast((x | y)): T;",
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }

    for source in ["cast([x): B;", "cast({x): B;", "cast(x: '[A): B;"] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
        assert_eq!(
            token_count(&declaration, SyntaxKind::RParen),
            1,
            "{source:?}"
        );
    }

    let source = "cast((x @): B;";
    let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);
    assert_eq!(count(&declaration, SyntaxKind::Error), 1);
    assert_eq!(token_count(&declaration, SyntaxKind::RParen), 1);
}

#[test]
fn cast_target_reuses_full_type_surface_with_nested_form_punctuation_suspended() {
    for source in [
        "cast(x): List(Int)::Result Arg -> Out -> Final;",
        "cast(x): F(:{A});",
        "cast(x): [e] F [io] -> U;",
        "cast(x): {field: A};",
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::CastTarget), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
        assert_eq!(
            token_count(&declaration, SyntaxKind::Semicolon),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn cast_pattern_prefix_and_close_recovery_is_bounded() {
    for (source, missing, errors) in [
        ("cast;", 1, 0),
        ("cast();", 2, 0),
        ("cast(@): B;", 0, 1),
        ("cast(x @ ): B;", 0, 1),
        ("cast @ (x): B;", 0, 1),
        ("cast @ : B;", 0, 1),
        ("cast @ = value", 0, 1),
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
    }

    let source = "cast x ) tail";
    let (green, exit, remainder) = run_cast_declaration(
        source,
        stops_for(TokenKind::RParen),
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "cast x");
    assert_eq!(remainder, " tail");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);
    assert_eq!(count(&declaration, SyntaxKind::Error), 0);
    assert_eq!(token_count(&declaration, SyntaxKind::RParen), 0);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::RParen));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");
}

#[test]
fn cast_target_and_form_recovery_keep_starters_distinct() {
    for (source, missing, errors, targets, bodies) in [
        ("cast(x) B;", 1, 0, 1, 0),
        ("cast(x) @ : B;", 0, 1, 1, 0),
        ("cast(x);", 1, 0, 0, 0),
        ("cast(x): ;", 1, 0, 1, 0),
        ("cast(x): @ ;", 0, 1, 1, 0),
        ("cast(x): B", 1, 0, 1, 0),
        ("cast(x): B = value", 0, 0, 1, 1),
        ("cast(x): B == value", 0, 1, 1, 0),
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
        assert_eq!(
            count(&declaration, SyntaxKind::CastTarget),
            targets,
            "{source:?}"
        );
        assert_eq!(
            count(&declaration, SyntaxKind::CastBody),
            bodies,
            "{source:?}"
        );
    }
}

#[test]
fn cast_malformed_body_introducer_retries_actual_form_starters() {
    for (source, form, body) in [
        ("cast(x): A @ ;", SyntaxKind::Semicolon, 0),
        ("cast(x): A @ = value", SyntaxKind::Equals, 1),
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(token_count(&declaration, form), 1, "{source:?}");
        assert_eq!(
            count(&declaration, SyntaxKind::CastBody),
            body,
            "{source:?}"
        );
        assert_eq!(
            crate::tests::recovery_output::recovery_groups(&declaration)
                .into_iter()
                .next()
                .expect("BodyIntroducer Error")
                .to_string(),
            "@",
            "{source:?}"
        );
    }
}

#[test]
fn cast_definition_body_preserves_boundaries_and_recovers_one_run() {
    for source in [
        "cast(x): T = value: argument",
        "cast(x): T = value with: body",
        "cast(x): T = value { field: x }",
        "cast(x): T =\r\n  my y = x\r\n  y",
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }

    let source = "cast(x): T = @ value";
    let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    let source = "cast(x): T = @   ";
    let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    assert_eq!(
        crate::tests::recovery_output::recovery_groups(&node)
            .into_iter()
            .next()
            .expect("PatternIntroducer Error")
            .to_string(),
        "@   "
    );

    let source = "cast(x): T = ; tail";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "cast(x): T =");
    assert_eq!(remainder, " tail");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let mut pending = pending_item(exit);
    assert_eq!(
        pending.payload_view().token_kind(),
        Some(TokenKind::Semicolon)
    );
    assert_eq!(emit_pending_leading_text(&mut pending), " ");

    let source = "cast(x): T =\ny";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "cast(x): T =");
    assert_eq!(remainder, "");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().spelling(), Some("y"));
    assert_eq!(emit_pending_leading_text(&mut pending), "\n");
}

#[test]
fn cast_phase_transitions_preserve_disallowed_newline_gaps() {
    for (source, accepted, pending_kind, leading, missing, errors) in [
        ("cast(x)\n;", "cast(x)", TokenKind::Semicolon, "\n", 1, 0),
        (
            "cast(x)\r\n;",
            "cast(x)",
            TokenKind::Semicolon,
            "\r\n",
            1,
            0,
        ),
        ("cast(x\n: T;", "cast(x", TokenKind::Colon, "\n", 1, 0),
        (
            "cast(x):\r\n= value",
            "cast(x):",
            TokenKind::Equals,
            "\r\n",
            1,
            0,
        ),
        (
            "cast(x):\n= value",
            "cast(x):",
            TokenKind::Equals,
            "\n",
            1,
            0,
        ),
        ("cast(@\n;", "cast(@", TokenKind::Semicolon, "\n", 0, 1),
        (
            "cast(x @\r\n: T;",
            "cast(x @",
            TokenKind::Colon,
            "\r\n",
            0,
            1,
        ),
        (
            "cast(x) @\n;",
            "cast(x) @",
            TokenKind::Semicolon,
            "\n",
            0,
            1,
        ),
    ] {
        let (green, exit, _) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), accepted, "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
        let mut pending = pending_item(exit);
        assert_eq!(pending.payload_view().token_kind(), Some(pending_kind));
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            leading,
            "{source:?}"
        );
    }

    for (source, missing) in [
        ("cast(x)\n  ;", 1),
        ("cast(x)\r\n  : T;", 0),
        ("cast(x):\n  = value", 1),
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }
}

#[test]
fn cast_malformed_pattern_introducer_owns_only_same_line_eof_trivia() {
    let source = "cast @   ";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    assert_eq!(
        crate::tests::recovery_output::recovery_groups(&node)
            .into_iter()
            .next()
            .expect("PatternIntroducer Error")
            .to_string(),
        "@   "
    );
    let mut pending = pending_item(exit);
    assert!(pending.payload_view().is_eof());
    assert_eq!(emit_pending_leading_text(&mut pending), "");

    for source in ["cast @\n", "cast @\r\n  "] {
        let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "cast @", "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(
            crate::tests::recovery_output::recovery_groups(&declaration)
                .into_iter()
                .next()
                .expect("PatternIntroducer Error")
                .to_string(),
            "@",
            "{source:?}"
        );
        let mut pending = pending_item(exit);
        assert!(pending.payload_view().is_eof());
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            &source["cast @".len()..],
            "{source:?}"
        );
    }
}

#[test]
fn cast_malformed_target_introducer_owns_only_same_line_eof_trivia() {
    let source = "cast(x) @   ";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    assert_eq!(
        crate::tests::recovery_output::recovery_groups(&node)
            .into_iter()
            .next()
            .expect("TargetIntroducer Error")
            .to_string(),
        "@   "
    );
    let mut pending = pending_item(exit);
    assert!(pending.payload_view().is_eof());
    assert_eq!(emit_pending_leading_text(&mut pending), "");

    for source in ["cast(x) @\n", "cast(x) @\r\n  "] {
        let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "cast(x) @", "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(
            crate::tests::recovery_output::recovery_groups(&declaration)
                .into_iter()
                .next()
                .expect("TargetIntroducer Error")
                .to_string(),
            "@",
            "{source:?}"
        );
        let mut pending = pending_item(exit);
        assert!(pending.payload_view().is_eof());
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            &source["cast(x) @".len()..],
            "{source:?}"
        );
    }
}

#[test]
fn cast_malformed_body_introducer_owns_only_same_line_eof_trivia() {
    let source = "cast(x): A @   ";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    assert_eq!(
        crate::tests::recovery_output::recovery_groups(&node)
            .into_iter()
            .next()
            .expect("BodyIntroducer Error")
            .to_string(),
        "@   "
    );
    let mut pending = pending_item(exit);
    assert!(pending.payload_view().is_eof());
    assert_eq!(emit_pending_leading_text(&mut pending), "");

    for source in ["cast(x): A @\n", "cast(x): A @\r\n  "] {
        let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "cast(x): A @", "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(
            crate::tests::recovery_output::recovery_groups(&declaration)
                .into_iter()
                .next()
                .expect("BodyIntroducer Error")
                .to_string(),
            "@",
            "{source:?}"
        );
        let mut pending = pending_item(exit);
        assert!(pending.payload_view().is_eof());
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            &source["cast(x): A @".len()..],
            "{source:?}"
        );
    }
}

#[test]
fn cast_malformed_body_owns_only_same_line_eof_trivia() {
    let source = "cast(x): A = @   ";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    assert_eq!(
        crate::tests::recovery_output::recovery_groups(&node)
            .into_iter()
            .next()
            .expect("Body Error")
            .to_string(),
        "@   "
    );
    let mut pending = pending_item(exit);
    assert!(pending.payload_view().is_eof());
    assert_eq!(emit_pending_leading_text(&mut pending), "");

    for source in ["cast(x): A = @\n", "cast(x): A = @\r\n  "] {
        let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "cast(x): A = @", "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(
            crate::tests::recovery_output::recovery_groups(&declaration)
                .into_iter()
                .next()
                .expect("Body Error")
                .to_string(),
            "@",
            "{source:?}"
        );
        let mut pending = pending_item(exit);
        assert!(pending.payload_view().is_eof());
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            &source["cast(x): A = @".len()..],
            "{source:?}"
        );
    }
}

#[test]
fn cast_indented_body_recovery_has_a_child_structural_fact() {
    let source = "cast(x): A =\n  ";
    let (green, _, facts, remainder) = typed_cast(source, 0, 0, None);
    assert_eq!(remainder, "");
    let declaration = declaration(&green);
    let indented = declaration
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("indented body owner");
    let missing = indented
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Missing)
        .expect("indented body Missing");
    let range = usize::from(missing.text_range().start())..usize::from(missing.text_range().end());
    assert_eq!(facts, [structural_fact(StructuralKind::Missing, range)]);
}

#[test]
fn cast_local_and_ambient_close_authority_preserves_exact_items() {
    let source = "cast([x ) ) tail";
    let (green, exit, remainder) = run_cast_declaration(
        source,
        stops_for(TokenKind::RParen),
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "cast([x )");
    assert_eq!(remainder, " tail");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Missing), 2);
    assert_eq!(token_count(&node, SyntaxKind::RParen), 1);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::RParen));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");

    let source = "cast([x } tail";
    let (green, exit, remainder) = run_cast_declaration(
        source,
        stops_for(TokenKind::RBrace),
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "cast([x");
    assert_eq!(remainder, " tail");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::RBrace));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");

    let source = "cast(x): T else tail";
    let (green, exit, remainder) =
        run_cast_declaration(source, STOP_ELSE, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "cast(x): T");
    assert_eq!(remainder, " tail");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().spelling(), Some("else"));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");
}

#[test]
fn cast_fence_and_origin_boundary_remain_outer_owned() {
    use crate::lexical::item::{BorrowedTarget, Boundary};
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
    let origin = 12_000;
    let accepted = "> > cast(x): T";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_cast_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let boundary = pending_item(exit);
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));

    let (_, _, facts, typed_remainder) =
        typed_cast_at(&source, origin, 0, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(typed_remainder, "> > ```\r\nouter");
    assert_eq!(
        facts,
        [structural_fact(
            StructuralKind::Missing,
            accepted.len()..accepted.len(),
        )]
    );

    let accepted = "> > cast(x): A =";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (_, _, facts, typed_remainder) =
        typed_cast_at(&source, origin, 0, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(typed_remainder, "> > ```\r\nouter");
    assert_eq!(
        facts,
        [structural_fact(
            StructuralKind::Missing,
            accepted.len()..accepted.len(),
        )]
    );

    let accepted = "> > cast @";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_cast_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::Error), 1);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 0);
    let boundary = pending_item(exit);
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));

    let (_, _, facts, typed_remainder) =
        typed_cast_at(&source, origin, 0, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(typed_remainder, "> > ```\r\nouter");
    assert_eq!(
        facts,
        [structural_fact(
            StructuralKind::ErrorGroup,
            "> > cast ".len()..accepted.len(),
        )]
    );

    let accepted = "> > cast(";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (_, _, facts, typed_remainder) =
        typed_cast_at(&source, origin, 0, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(typed_remainder, "> > ```\r\nouter");
    assert_eq!(
        facts,
        [structural_fact(
            StructuralKind::Missing,
            accepted.len()..accepted.len(),
        )]
    );

    let accepted = "> > cast(x) @";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (_, _, facts, typed_remainder) =
        typed_cast_at(&source, origin, 0, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(typed_remainder, "> > ```\r\nouter");
    assert_eq!(
        facts,
        [structural_fact(
            StructuralKind::ErrorGroup,
            "> > cast(x) ".len()..accepted.len(),
        )]
    );

    let accepted = "> > cast(x): A @";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (_, _, facts, typed_remainder) =
        typed_cast_at(&source, origin, 0, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(typed_remainder, "> > ```\r\nouter");
    assert_eq!(
        facts,
        [structural_fact(
            StructuralKind::ErrorGroup,
            "> > cast(x): A ".len()..accepted.len(),
        )]
    );
}

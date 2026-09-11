use crate::tests::support::*;

// The matrix reads native ordered Rowan children, including adjacent Error
// fragments and the ordinary trivia that ends their run; no Error spelling or
// parser recovery records participate in selecting a slot.
fn assert_use_schema_children(
    source: &str,
    owner: SyntaxKind,
    ancestors: &[SyntaxKind],
    expected: &[(SyntaxKind, std::ops::Range<u32>)],
) {
    assert_use_schema_occurrence(source, owner, 0, ancestors, expected);
}

fn assert_use_schema_occurrence(
    source: &str,
    owner: SyntaxKind,
    occurrence: usize,
    ancestors: &[SyntaxKind],
    expected: &[(SyntaxKind, std::ops::Range<u32>)],
) {
    let (green, _) = run_statement(source);
    let declaration = use_declaration(&green);
    assert_eq!(declaration.to_string(), source);
    let node = declaration
        .descendants()
        .filter(|node| node.kind() == owner)
        .nth(occurrence)
        .unwrap();
    assert_eq!(
        node.ancestors()
            .take(ancestors.len())
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        ancestors,
        "{source:?}",
    );
    assert_eq!(
        node.children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    u32::from(range.start())..u32::from(range.end()),
                )
            })
            .collect::<Vec<_>>(),
        expected,
        "{source:?}",
    );
}

// Foreign/local-close recovery and OperatorName close slots remain outside
// this matrix pending the user decision on their CST topology.
#[test]
fn use_schema_accepted_group_children_and_nested_occurrences() {
    use SyntaxKind::*;
    assert_use_schema_children(
        "use {a,b}",
        UseGroup,
        &[UseGroup, UseTree, UseDeclaration, Statement],
        &[
            (LBrace, 4..5),
            (UseTree, 5..6),
            (Comma, 6..7),
            (UseTree, 7..8),
            (RBrace, 8..9),
        ],
    );
    let source = "use {a,{b,c}}";
    assert_use_schema_children(
        source,
        UseGroup,
        &[UseGroup, UseTree, UseDeclaration, Statement],
        &[
            (LBrace, 4..5),
            (UseTree, 5..6),
            (Comma, 6..7),
            (UseTree, 7..12),
            (RBrace, 12..13),
        ],
    );
    assert_use_schema_occurrence(
        source,
        UseTree,
        2,
        &[UseTree, UseGroup, UseTree, UseDeclaration, Statement],
        &[(UseGroup, 7..12)],
    );
    assert_use_schema_occurrence(
        source,
        UseGroup,
        1,
        &[
            UseGroup,
            UseTree,
            UseGroup,
            UseTree,
            UseDeclaration,
            Statement,
        ],
        &[
            (LBrace, 7..8),
            (UseTree, 8..9),
            (Comma, 9..10),
            (UseTree, 10..11),
            (RBrace, 11..12),
        ],
    );
}

#[test]
fn use_schema_parenthesized_exclusion_group_children() {
    use SyntaxKind::*;
    assert_use_schema_children(
        "use x::* without (a,b)",
        UseExclusionGroup,
        &[
            UseExclusionGroup,
            UseExclusion,
            UseGlob,
            UseTree,
            UseDeclaration,
            Statement,
        ],
        &[
            (LParen, 17..18),
            (UseTree, 18..19),
            (Comma, 19..20),
            (UseTree, 20..21),
            (RParen, 21..22),
        ],
    );
}

#[test]
fn use_schema_path_and_alias_share_one_ordered_tree() {
    use SyntaxKind::*;
    assert_use_schema_children(
        "use p::q as r",
        UseTree,
        &[UseTree, UseDeclaration, Statement],
        &[(UsePath, 4..8), (Whitespace, 8..9), (UseAlias, 9..13)],
    );
}

#[test]
fn use_schema_utf8_path_missing_uses_byte_range() {
    use SyntaxKind::*;
    assert_use_schema_children(
        "use 猫::",
        UsePath,
        &[UsePath, UseTree, UseDeclaration, Statement],
        &[(Identifier, 4..7), (ColonColon, 7..9), (Missing, 9..9)],
    );
}

#[test]
fn use_schema_initial_path_and_separator_retry_phases() {
    use SyntaxKind::*;
    for (source, expected) in [
        ("use", vec![(UseKw, 0..3), (Missing, 3..3)]),
        (
            "use @ #",
            vec![
                (UseKw, 0..3),
                (Whitespace, 3..4),
                (Error, 4..5),
                (Error, 5..6),
                (Error, 6..7),
            ],
        ),
        (
            "use @ # p",
            vec![
                (UseKw, 0..3),
                (Whitespace, 3..4),
                (Error, 4..5),
                (Error, 5..6),
                (Error, 6..7),
                (Whitespace, 7..8),
                (UseTree, 8..9),
            ],
        ),
    ] {
        assert_use_schema_children(
            source,
            UseDeclaration,
            &[UseDeclaration, Statement],
            &expected,
        );
    }
    for (separator, kind) in [("::", ColonColon), ("/", Slash)] {
        let end = 5 + separator.len() as u32;
        for suffix in ["", "@ #", "@ # q"] {
            let mut expected = vec![(Identifier, 4..5), (kind, 5..end)];
            if suffix.is_empty() {
                expected.push((Missing, end..end));
            } else {
                expected.extend([
                    (Error, end..end + 1),
                    (Error, end + 1..end + 2),
                    (Error, end + 2..end + 3),
                ]);
                if suffix.ends_with('q') {
                    expected.extend([
                        (Whitespace, end + 3..end + 4),
                        (Identifier, end + 4..end + 5),
                    ]);
                }
            }
            assert_use_schema_children(
                &format!("use p{separator}{suffix}"),
                UsePath,
                &[UsePath, UseTree, UseDeclaration, Statement],
                &expected,
            );
        }
    }
}

#[test]
fn use_schema_alias_identifier_missing_terminal_and_retry() {
    use SyntaxKind::*;
    for (source, expected) in [
        ("use p as", vec![(AsKw, 6..8), (Missing, 8..8)]),
        (
            "use p as @ #",
            vec![
                (AsKw, 6..8),
                (Whitespace, 8..9),
                (Error, 9..10),
                (Error, 10..11),
                (Error, 11..12),
            ],
        ),
        (
            "use p as @ # q",
            vec![
                (AsKw, 6..8),
                (Whitespace, 8..9),
                (Error, 9..10),
                (Error, 10..11),
                (Error, 11..12),
                (Whitespace, 12..13),
                (Identifier, 13..14),
            ],
        ),
    ] {
        assert_use_schema_children(
            source,
            UseAlias,
            &[UseAlias, UseTree, UseDeclaration, Statement],
            &expected,
        );
    }
}

#[test]
fn use_schema_group_entry_and_post_child_separator_missing() {
    use SyntaxKind::*;
    for (source, expected) in [
        (
            "use {,}",
            vec![
                (LBrace, 4..5),
                (Missing, 5..5),
                (Comma, 5..6),
                (RBrace, 6..7),
            ],
        ),
        (
            "use {a b}",
            vec![
                (LBrace, 4..5),
                (UseTree, 5..6),
                (Whitespace, 6..7),
                (Missing, 7..7),
                (UseTree, 7..8),
                (RBrace, 8..9),
            ],
        ),
    ] {
        assert_use_schema_children(
            source,
            UseGroup,
            &[UseGroup, UseTree, UseDeclaration, Statement],
            &expected,
        );
    }
    for (source, expected) in [
        (
            "use x::* without {,}",
            vec![
                (LBrace, 17..18),
                (Missing, 18..18),
                (Comma, 18..19),
                (RBrace, 19..20),
            ],
        ),
        (
            "use x::* without {a b}",
            vec![
                (LBrace, 17..18),
                (UseTree, 18..19),
                (Whitespace, 19..20),
                (Missing, 20..20),
                (UseTree, 20..21),
                (RBrace, 21..22),
            ],
        ),
    ] {
        assert_use_schema_children(
            source,
            UseExclusionGroup,
            &[
                UseExclusionGroup,
                UseExclusion,
                UseGlob,
                UseTree,
                UseDeclaration,
                Statement,
            ],
            &expected,
        );
    }
}

fn use_declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::UseDeclaration)
        .expect("UseDeclaration")
}

fn descendants_of_kind(node: &SyntaxNode, kind: SyntaxKind) -> usize {
    if kind == SyntaxKind::Error {
        return crate::tests::recovery_output::recovery_groups(node).len();
    }
    node.descendants()
        .filter(|descendant| descendant.kind() == kind)
        .count()
}

#[test]
fn use_c9_builds_all_visibility_and_form_heads() {
    for (source, visibility, form) in [
        ("use std::data", None, None),
        (
            "my use realm/tools::format",
            Some(SyntaxKind::MyKw),
            Some(SyntaxKind::RealmKw),
        ),
        (
            "our use band::support::value",
            Some(SyntaxKind::OurKw),
            Some(SyntaxKind::BandKw),
        ),
        (
            "pub use mod math::value",
            Some(SyntaxKind::PubKw),
            Some(SyntaxKind::ModKw),
        ),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = use_declaration(&green);
        assert_eq!(
            declaration.parent().map(|node| node.kind()),
            Some(SyntaxKind::Statement)
        );
        assert_eq!(
            declaration
                .children()
                .filter(|node| node.kind() == SyntaxKind::UseTree)
                .count(),
            1
        );
        assert_eq!(
            visibility.map(|kind| {
                declaration
                    .children_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(|token| token.kind() == kind)
            }),
            visibility.map(|_| true),
            "{source:?}"
        );
        assert_eq!(
            form.map(|kind| {
                declaration
                    .descendants_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(|token| token.kind() == kind)
            }),
            form.map(|_| true),
            "{source:?}"
        );
    }

    for source in ["use realm::x", "use band/x", "use other/x::y"] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        let declaration = use_declaration(&green);
        assert!(
            !declaration
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| matches!(token.kind(), SyntaxKind::RealmKw | SyntaxKind::BandKw))
        );
    }
}

#[test]
fn use_c9_keeps_recursive_groups_and_operator_segments_structured() {
    let source = "use std::io::{read, write,\n nested::{(+), {leaf,}}}";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let declaration = use_declaration(&green);
    assert_eq!(descendants_of_kind(&declaration, SyntaxKind::UseGroup), 3);
    assert_eq!(
        descendants_of_kind(&declaration, SyntaxKind::OperatorName),
        1
    );
    let operator = declaration
        .descendants()
        .find(|node| node.kind() == SyntaxKind::OperatorName)
        .expect("OperatorName");
    assert_eq!(operator.text().to_string(), "(+)");
    assert_eq!(
        operator
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::LParen, SyntaxKind::Operator, SyntaxKind::RParen]
    );

    for source in [
        "use {}",
        "use {/* newline in comment\n */ a\n b,}",
        "use realm/{a}",
        "use band::*",
        "use (+)::map",
        "use std::(+)",
        "use path as first as second",
        "use {a} as all",
        "use {a\n  use\n  my\n  our\n  pub}",
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
    }
}

#[test]
fn use_c9_builds_glob_alias_exclusions_version_and_anchor_in_source_order() {
    let source = "use std::* as all as everything without {foo, (*), nested::{x, y}}, bar, * v1-alpha+build.2 with program::ui";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let declaration = use_declaration(&green);
    let glob = declaration
        .descendants()
        .find(|node| node.kind() == SyntaxKind::UseGlob)
        .expect("UseGlob");
    assert_eq!(descendants_of_kind(&glob, SyntaxKind::UseAlias), 2);
    assert_eq!(descendants_of_kind(&glob, SyntaxKind::UseExclusion), 3);
    assert_eq!(descendants_of_kind(&glob, SyntaxKind::UseExclusionGroup), 1);
    assert!(
        glob.children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::WithoutKw)
    );

    let qualifiers = declaration
        .descendants()
        .find(|node| node.kind() == SyntaxKind::UseQualifiers)
        .expect("UseQualifiers");
    assert_eq!(
        qualifiers
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::UseVersion, SyntaxKind::UseAnchor]
    );
    assert_eq!(
        qualifiers
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == SyntaxKind::Version)
            .map(|token| token.text().to_string())
            .as_deref(),
        Some("v1-alpha+build.2")
    );

    let source = "use std::* without (*)";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let exclusion = use_declaration(&green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::UseExclusion)
        .expect("UseExclusion");
    assert_eq!(
        exclusion.first_child().map(|node| node.kind()),
        Some(SyntaxKind::OperatorName)
    );

    let source = "use std::* without (foo, bar)";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let declaration = use_declaration(&green);
    assert_eq!(
        descendants_of_kind(&declaration, SyntaxKind::UseExclusionGroup),
        1
    );
    assert_eq!(
        descendants_of_kind(&declaration, SyntaxKind::OperatorName),
        0
    );
}

#[test]
fn use_c9_dispatch_is_exact_contextual_and_shared_with_binding() {
    for source in ["use path", "my use path", "our use path", "pub use path"] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::UseDeclaration)
        );
    }

    for source in ["useful", "useful path"] {
        let (green, _) = run_statement(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::UseDeclaration)
        );
    }

    for source in ["my use = value", "my use", "my use @ path"] {
        let (green, _) = run_statement(source);
        let root = SyntaxNode::new_root(green);
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::BindingStatement),
            "{source:?}"
        );
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::UseDeclaration),
            "{source:?}"
        );
    }

    let (green, _) = run_statement("use");
    let declaration = use_declaration(&green);
    assert_eq!(descendants_of_kind(&declaration, SyntaxKind::Missing), 1);

    for source in ["our use", "pub use"] {
        let (green, _) = run_statement(source);
        let declaration = use_declaration(&green);
        assert_eq!(green.to_string(), source);
        assert_eq!(descendants_of_kind(&declaration, SyntaxKind::Missing), 1);
    }
}

#[test]
fn use_c9_classifies_reserved_use_atoms_before_identifier_slots() {
    let controls = [
        ("use v1", "use v1", "v1", 0, 1),
        ("use mod as", "use mod ", "as", 1, 0),
        ("use a::with", "use a::", "with", 1, 0),
        ("use a as without", "use a as ", "without", 1, 0),
    ];
    for (source, owned, pending, missing, error) in controls {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), owned, "{source:?}");
        let declaration = use_declaration(&green);
        assert_eq!(
            descendants_of_kind(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(
            descendants_of_kind(&declaration, SyntaxKind::Error),
            error,
            "{source:?}"
        );
        assert!(
            !declaration
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Identifier && token.text() == pending),
            "{source:?}"
        );
        if owned != source {
            assert!(matches!(
                exit,
                Some(Err(Either::Left(item)))
                    if item.payload_view().spelling() == Some(pending)
            ));
        }
    }
}

#[test]
fn use_c9_totalizes_mandatory_slots_and_retries_once() {
    for (source, missing, error) in [
        ("use", 1, 0),
        ("use @ path", 0, 1),
        ("use @ /*not a path*/ path", 0, 1),
        ("use std::", 1, 0),
        ("use std::{a b}", 1, 0),
        ("use std::{a", 1, 0),
        ("use std::* as", 1, 0),
        ("use std::* without", 1, 0),
        ("use std v1 with", 1, 0),
        ("use path:: as alias", 1, 0),
        ("use path:: v1", 1, 0),
        ("use path:: with anchor", 1, 0),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = use_declaration(&green);
        assert_eq!(
            descendants_of_kind(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(
            descendants_of_kind(&declaration, SyntaxKind::Error),
            error,
            "{source:?}"
        );
    }

    for source in [
        "use path::@leaf",
        "use path as @ alias",
        "use path with @ anchor",
        "use path::* without @ excluded",
        "use {@ child}",
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = use_declaration(&green);
        assert_eq!(
            descendants_of_kind(&declaration, SyntaxKind::Missing),
            0,
            "{source:?}"
        );
        assert_eq!(
            descendants_of_kind(&declaration, SyntaxKind::Error),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn use_c9_requires_an_immediate_operator_after_a_path_open() {
    for (source, operator_names, missing, errors) in [
        ("use a::(", 0, 0, 1),
        ("use a::(foo", 0, 0, 1),
        ("use a::(+)", 1, 0, 0),
    ] {
        let (green, exit) = run_statement(source);
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::OperatorName)
                .count(),
            operator_names,
            "{source:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}",
        );
        assert_eq!(
            crate::tests::recovery_output::recovery_groups(&root)
                .into_iter()
                .count(),
            errors,
            "{source:?}",
        );
    }
}

#[test]
fn use_c9_leaves_statement_boundaries_for_the_caller() {
    for source in ["use path; next", "use path, next", "use path}next"] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), "use path", "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Left(_)))), "{source:?}");
    }

    let (green, exit) = run_statement("use path\nnext");
    assert_eq!(green.to_string(), "use path");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.leading_view().has_ordinary_newline()
    ));

    let (green, exit) = run_statement("use /* boundary\n */ next");
    assert_eq!(green.to_string(), "use");
    let Some(Err(Either::Left(mut item))) = exit else {
        panic!("block-comment boundary must remain pending")
    };
    assert_eq!(
        emit_pending_leading_tokens(&mut item),
        [
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::BlockComment, "/* boundary\n */".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned())
        ]
    );
    assert_eq!(
        descendants_of_kind(&use_declaration(&green), SyntaxKind::Missing),
        1
    );

    let source = "{use a;  use b}";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::UseDeclaration)
            .count(),
        2
    );
    assert!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::UseDeclaration)
            .all(|node| !node
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Semicolon))
    );

    let operators = OperatorTable::empty();
    let (green, exit) = run_statement_with_stops("use @  -> next", &operators, STOP_ARROW);
    assert_eq!(green.to_string(), "use @");
    let Some(Err(Either::Left(mut item))) = exit else {
        panic!("arrow must remain pending")
    };
    assert_eq!(token_kind(&item), Some(TokenKind::Arrow));
    assert_eq!(emit_pending_leading_text(&mut item), "  ");

    let (green, exit) = run_statement("use  [next");
    assert_eq!(green.to_string(), "use");
    let Some(Err(Either::Left(mut item))) = exit else {
        panic!("bracket must remain pending")
    };
    assert_eq!(token_kind(&item), Some(TokenKind::LBracket));
    assert_eq!(emit_pending_leading_text(&mut item), "  ");
}

#[test]
fn use_c9_missing_group_close_hands_equal_indent_statement_intro_to_caller() {
    let (green, exit) = run_statement("use {a\nuse b");
    assert_eq!(green.to_string(), "use {a");
    assert_eq!(
        descendants_of_kind(&use_declaration(&green), SyntaxKind::Missing),
        1
    );
    let Some(Err(Either::Left(mut item))) = exit else {
        panic!("use intro must remain pending")
    };
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    assert_eq!(item.payload_view().spelling(), Some("use"));
    assert_eq!(emit_pending_leading_text(&mut item), "\n");

    let (green, exit) = run_statement("use {a\ntype T = A");
    assert_eq!(green.to_string(), "use {a");
    assert_eq!(
        descendants_of_kind(&use_declaration(&green), SyntaxKind::Missing),
        1
    );
    let Some(Err(Either::Left(mut item))) = exit else {
        panic!("type intro must remain pending")
    };
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    assert_eq!(item.payload_view().spelling(), Some("type"));
    assert_eq!(emit_pending_leading_text(&mut item), "\n");

    for source in ["use {a\n  use b}", "use {a\nuseful}"] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
    }
}

#[test]
fn use_c9_recovers_local_group_mismatches_without_stealing_outer_closes() {
    for source in ["use {a) b}", "use x::* without (a} b)"] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = use_declaration(&green);
        assert_eq!(
            descendants_of_kind(&declaration, SyntaxKind::Error),
            1,
            "{source:?}"
        );
    }

    let source = "use {x::* without (a}";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let declaration = use_declaration(&green);
    assert_eq!(descendants_of_kind(&declaration, SyntaxKind::Error), 0);
    assert_eq!(descendants_of_kind(&declaration, SyntaxKind::Missing), 1);
    assert_eq!(
        declaration
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::RBrace)
            .count(),
        1
    );

    let operators = OperatorTable::empty();
    let (green, exit) =
        run_statement_with_stops("use {a  )next", &operators, stops_for(TokenKind::RParen));
    assert_eq!(green.to_string(), "use {a");
    let Some(Err(Either::Left(mut item))) = exit else {
        panic!("caller close must remain pending")
    };
    assert_eq!(token_kind(&item), Some(TokenKind::RParen));
    assert_eq!(emit_pending_leading_text(&mut item), "  ");
}

#[test]
fn use_c9_reaches_every_canonical_statement_site_but_not_inline_expression_sites() {
    for source in [
        "{use a; x}",
        "f:\n  use a\n  x",
        "if c:\n  use a\n  x",
        "case x:\n  p ->\n    use a\n    x",
        "catch action:\n  err ->\n    use a\n    recover",
        "value with: use a",
        "value with:\n  use a\n  x",
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::UseDeclaration),
            "{source:?}"
        );
    }

    let source = "my x =\n  use a\n  x";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::UseDeclaration)
    );

    for source in [
        "f: use a",
        "if c: use a",
        "case x: p -> use a",
        "catch action: err -> use a",
    ] {
        let (green, _) = run(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::UseDeclaration),
            "{source:?}"
        );
    }
}

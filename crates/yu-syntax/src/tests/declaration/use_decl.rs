use crate::tests::support::*;

#[test]
fn use_glob_outer_comma_accepts_newline_leading() {
    use SyntaxKind::*;

    for gap in ["\n", "\r\n  ", " /* comment\n */ "] {
        let source = format!("use p::* without a,{gap}b");
        let (green, exit) = run_statement(&source);
        assert_eq!(green.to_string(), source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let declaration = use_declaration(&green);
        assert_eq!(descendants_of_kind(&declaration, Missing), 0);
        assert_eq!(descendants_of_kind(&declaration, Error), 0);
        let glob = declaration
            .descendants()
            .find(|node| node.kind() == UseGlob)
            .unwrap();
        let children: Vec<_> = glob.children_with_tokens().collect();
        let comma = children
            .iter()
            .position(|child| child.kind() == Comma)
            .unwrap();
        assert_eq!(
            children[comma + 1..children.len() - 1]
                .iter()
                .map(ToString::to_string)
                .collect::<String>(),
            gap
        );
        assert!(
            children[comma + 1..children.len() - 1]
                .iter()
                .all(|child| child.as_token().is_some())
        );
        assert_eq!(children.last().unwrap().kind(), UseExclusion);
        assert_eq!(children.last().unwrap().to_string(), "b");
    }

    for newline in ["\n", "\r\n"] {
        let source = format!("if c:{newline}  use p::* without a,{newline}    b{newline}  x");
        let (green, exit) = run(&source);
        assert_eq!(green.to_string(), source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let declaration = use_declaration(&green);
        assert_eq!(descendants_of_kind(&declaration, UseExclusion), 2);
        assert_eq!(descendants_of_kind(&declaration, Missing), 0);
        assert_eq!(descendants_of_kind(&declaration, Error), 0);
        assert!(declaration.to_string().ends_with('b'));
    }
}

#[test]
fn use_glob_outer_comma_preserves_protected_boundaries() {
    for suffix in ["\n;next", "\r\n)next", "\n]next", "\n}next", "\n,next"] {
        let source = format!("use p::* without a,{suffix}");
        let (green, exit) = run_statement(&source);
        assert_eq!(green.to_string(), "use p::* without a,");
        assert_eq!(
            descendants_of_kind(&use_declaration(&green), SyntaxKind::Missing),
            1
        );
        let Some(Err(Either::Left(mut pending))) = exit else {
            panic!("protected token must remain pending")
        };
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            if suffix.starts_with("\r\n") {
                "\r\n"
            } else {
                "\n"
            }
        );
    }

    for suffix in ["\nb", " ,b", "\n,b"] {
        let source = format!("use p::* without a{suffix}");
        let (green, exit) = run_statement(&source);
        assert_eq!(green.to_string(), "use p::* without a");
        assert!(matches!(exit, Some(Err(Either::Left(_)))));
        assert_eq!(
            descendants_of_kind(&use_declaration(&green), SyntaxKind::UseExclusion),
            1
        );
    }
}

#[test]
fn use_schema_full_tree_accepted_composition() {
    use SyntaxKind::*;

    // Component matrices below own their internals; this gate fixes their
    // source-ordered composition, including marker and terminal-join ownership.
    for (source, tree_text, children) in [
        ("use {}", "{}", vec![(UseGroup, "{}")]),
        ("use (+)::p", "(+)::p", vec![(UsePath, "(+)::p")]),
        ("use p::(+)", "p::(+)", vec![(UsePath, "p::(+)")]),
        (
            "use mod p::(+) v1",
            "mod p::(+) v1",
            vec![
                (ModKw, "mod"),
                (Whitespace, " "),
                (UsePath, "p::(+)"),
                (UseQualifiers, " v1"),
            ],
        ),
        (
            "use mod p::* v1",
            "mod p::* v1",
            vec![
                (ModKw, "mod"),
                (Whitespace, " "),
                (UsePath, "p"),
                (ColonColon, "::"),
                (UseGlob, "*"),
                (UseQualifiers, " v1"),
            ],
        ),
        (
            "use mod p::{x} as q v1 with a",
            "mod p::{x} as q v1 with a",
            vec![
                (ModKw, "mod"),
                (Whitespace, " "),
                (UsePath, "p"),
                (ColonColon, "::"),
                (UseGroup, "{x}"),
                (Whitespace, " "),
                (UseAlias, "as q"),
                (UseQualifiers, " v1 with a"),
            ],
        ),
        (
            "use realm/p",
            "realm/p",
            vec![(RealmKw, "realm"), (Slash, "/"), (UsePath, "p")],
        ),
        (
            "use band::p",
            "band::p",
            vec![(BandKw, "band"), (ColonColon, "::"), (UsePath, "p")],
        ),
        (
            "use realm/{x}",
            "realm/{x}",
            vec![(RealmKw, "realm"), (Slash, "/"), (UseGroup, "{x}")],
        ),
        (
            "use band::{x}",
            "band::{x}",
            vec![(BandKw, "band"), (ColonColon, "::"), (UseGroup, "{x}")],
        ),
        (
            "use band::*",
            "band::*",
            vec![(BandKw, "band"), (ColonColon, "::"), (UseGlob, "*")],
        ),
        ("use realm::p", "realm::p", vec![(UsePath, "realm::p")]),
        ("use band/p", "band/p", vec![(UsePath, "band/p")]),
        ("use p/q", "p/q", vec![(UsePath, "p/q")]),
        (
            "use p/{x}",
            "p/{x}",
            vec![(UsePath, "p"), (Slash, "/"), (UseGroup, "{x}")],
        ),
        (
            "use p as a as b v1 with anchor",
            "p as a as b v1 with anchor",
            vec![
                (UsePath, "p"),
                (Whitespace, " "),
                (UseAlias, "as a"),
                (Whitespace, " "),
                (UseAlias, "as b"),
                (UseQualifiers, " v1 with anchor"),
            ],
        ),
        (
            "use p v1",
            "p v1",
            vec![(UsePath, "p"), (UseQualifiers, " v1")],
        ),
        (
            "use p with a",
            "p with a",
            vec![(UsePath, "p"), (UseQualifiers, " with a")],
        ),
        (
            "use p::* as a without b v1 with anchor",
            "p::* as a without b v1 with anchor",
            vec![
                (UsePath, "p"),
                (ColonColon, "::"),
                (UseGlob, "* as a without b"),
                (UseQualifiers, " v1 with anchor"),
            ],
        ),
        (
            "use band::* as a v1 with anchor",
            "band::* as a v1 with anchor",
            vec![
                (BandKw, "band"),
                (ColonColon, "::"),
                (UseGlob, "* as a"),
                (UseQualifiers, " v1 with anchor"),
            ],
        ),
        (
            "use {p::{x} as q v1}",
            "{p::{x} as q v1}",
            vec![(UseGroup, "{p::{x} as q v1}")],
        ),
        (
            "use {p::{x} as q v1}",
            "p::{x} as q v1",
            vec![
                (UsePath, "p"),
                (ColonColon, "::"),
                (UseGroup, "{x}"),
                (Whitespace, " "),
                (UseAlias, "as q"),
                (UseQualifiers, " v1"),
            ],
        ),
    ] {
        let (green, records) = use_group_recoveries(source, None);
        let root = SyntaxNode::new_root(green.clone());
        assert_eq!(root.to_string(), source);
        assert!(records.is_empty(), "{source:?}");
        assert!(
            root.descendants_with_tokens().all(|child| !matches!(
                child.kind(),
                Missing | Error | Invalid | UseGroupForeignClose
            )),
            "{source:?}"
        );
        let tree = root
            .descendants()
            .find(|node| node.kind() == UseTree && node.to_string() == tree_text)
            .unwrap();
        assert_use_composition_children(&tree, source.find(tree_text).unwrap() as u32, &children);
        let parent = tree.parent().unwrap();
        assert_eq!(
            parent.kind(),
            if tree_text == &source[4..] {
                UseDeclaration
            } else {
                UseGroup
            }
        );
        if tree_text.contains("* as a") {
            let alias = tree
                .descendants()
                .find(|node| node.kind() == UseAlias)
                .unwrap();
            assert_eq!(alias.to_string(), "as a");
            assert_eq!(
                alias
                    .ancestors()
                    .take(3)
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                [UseAlias, UseGlob, UseTree]
            );
        }
        let (frozen, frozen_records) = use_group_recoveries(source, Some(&records));
        assert_eq!(green, frozen, "{source:?}");
        assert_eq!(records, frozen_records, "{source:?}");
    }
}

#[test]
fn use_schema_full_tree_recovered_and_protected_composition() {
    use SyntaxKind::*;

    for (source, children, recovery) in [
        (
            "use mod",
            vec![(ModKw, "mod"), (UsePath, "")],
            vec![(Missing, UsePath, 7..7)],
        ),
        (
            "use mod @",
            vec![(ModKw, "mod"), (UsePath, " @")],
            vec![(Error, UsePath, 8..9)],
        ),
        (
            "use mod @ p",
            vec![(ModKw, "mod"), (UsePath, " @ p")],
            vec![(Error, UsePath, 8..9)],
        ),
        (
            "use realm/@ p",
            vec![(RealmKw, "realm"), (Slash, "/"), (UsePath, "@ p")],
            vec![(Error, UsePath, 10..11)],
        ),
        (
            "use p::",
            vec![(UsePath, "p::")],
            vec![(Missing, UsePath, 7..7)],
        ),
        (
            "use p::@ q",
            vec![(UsePath, "p::@ q")],
            vec![(Error, UsePath, 7..8)],
        ),
        (
            "use (+",
            vec![(UsePath, "(+")],
            vec![(Missing, OperatorName, 6..6)],
        ),
        (
            "use p as",
            vec![(UsePath, "p"), (Whitespace, " "), (UseAlias, "as")],
            vec![(Missing, UseAlias, 8..8)],
        ),
        (
            "use p as @ q",
            vec![(UsePath, "p"), (Whitespace, " "), (UseAlias, "as @ q")],
            vec![(Error, UseAlias, 9..10)],
        ),
        (
            "use {a b}",
            vec![(UseGroup, "{a b}")],
            vec![(Missing, UseGroup, 7..7)],
        ),
        (
            "use {@ a}",
            vec![(UseGroup, "{@ a}")],
            vec![(Error, UseGroup, 5..6)],
        ),
        (
            "use p::* without",
            vec![(UsePath, "p"), (ColonColon, "::"), (UseGlob, "* without")],
            vec![(Missing, UseGlob, 16..16)],
        ),
        (
            "use p::* without @ a v1",
            vec![
                (UsePath, "p"),
                (ColonColon, "::"),
                (UseGlob, "* without @ a"),
                (UseQualifiers, " v1"),
            ],
            vec![(Error, UseGlob, 17..18)],
        ),
        (
            "use p with @ a",
            vec![(UsePath, "p"), (UseQualifiers, " with @ a")],
            vec![(Error, UsePath, 11..12)],
        ),
        (
            "use mod ;next",
            vec![(ModKw, "mod"), (UsePath, "")],
            vec![(Missing, UsePath, 7..7)],
        ),
        (
            "use p:: ;next",
            vec![(UsePath, "p::")],
            vec![(Missing, UsePath, 7..7)],
        ),
        (
            "use p as ;next",
            vec![(UsePath, "p"), (Whitespace, " "), (UseAlias, "as")],
            vec![(Missing, UseAlias, 8..8)],
        ),
        (
            "use {a ;next",
            vec![(UseGroup, "{a")],
            vec![(Missing, UseGroup, 6..6)],
        ),
        (
            "use p::* without ;next",
            vec![(UsePath, "p"), (ColonColon, "::"), (UseGlob, "* without")],
            vec![(Missing, UseGlob, 16..16)],
        ),
        (
            "use p::* without a ;next",
            vec![(UsePath, "p"), (ColonColon, "::"), (UseGlob, "* without a")],
            vec![],
        ),
        (
            "use p with ;next",
            vec![(UsePath, "p"), (UseQualifiers, " with")],
            vec![(Missing, UsePath, 10..10)],
        ),
    ] {
        let operators = OperatorTable::empty();
        let mut previous: Option<(GreenNode, Vec<CommittedRecoveryRecord>)> = None;
        for _ in 0..2 {
            let mut input = source;
            let mut recover = match &previous {
                Some((_, records)) => Recover::reconcile_for_test(&operators, records),
                None => Recover::new_for_test(&operators),
            };
            let mut builder = GreenNodeBuilder::new();
            builder.start_node(Root.into());
            let mut exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
            if let Err(Either::Right(end)) = &mut exit {
                emit_end(&mut builder, end);
            }
            builder.finish_node();
            let green = builder.finish();
            let records = recover.finish_recoveries_for_test();
            let root = SyntaxNode::new_root(green.clone());
            let tree = root
                .descendants()
                .find(|node| node.kind() == UseTree)
                .unwrap();
            assert_eq!(tree.parent().unwrap().kind(), UseDeclaration);
            assert_use_composition_children(&tree, 4, &children);
            assert_eq!(
                root.descendants_with_tokens()
                    .filter(|child| matches!(child.kind(), Missing | Error))
                    .map(|child| {
                        let range = child.text_range();
                        (
                            child.kind(),
                            child.parent().unwrap().kind(),
                            u32::from(range.start())..u32::from(range.end()),
                        )
                    })
                    .collect::<Vec<_>>(),
                recovery,
                "{source:?}"
            );
            for node in root.descendants().filter(|node| node.kind() == UseTree) {
                assert!(node.children_with_tokens().all(|child| !matches!(
                    child.kind(),
                    Missing | Error | Invalid | UseGroupForeignClose
                )));
            }
            for child in root.descendants_with_tokens() {
                let range = child.text_range();
                assert_eq!(
                    child.to_string(),
                    source[usize::from(range.start())..usize::from(range.end())]
                );
            }
            if let Some(boundary) = source.find(" ;next") {
                assert_eq!(root.to_string(), source[..boundary]);
                let Err(Either::Left(mut item)) = exit else {
                    panic!("protected semicolon must remain pending: {source:?}")
                };
                assert_eq!(token_kind(&item), Some(TokenKind::Semicolon));
                assert_eq!(item.payload_view().spelling(), Some(";"));
                let extent = item.extent(source.len() - input.len());
                assert_eq!(extent.leading(), boundary..boundary + 1);
                assert_eq!(extent.payload(), boundary + 1..boundary + 2);
                let leading = emit_pending_leading_text(&mut item);
                assert_eq!(leading, " ");
                assert_eq!(input, "next");
                assert_eq!(format!("{root}{leading};{input}"), source);
            } else {
                assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
                assert_eq!(input, "");
                assert_eq!(root.to_string(), source);
            }
            if let Some((fresh, fresh_records)) = &previous {
                assert_eq!(&green, fresh, "{source:?}");
                assert_eq!(&records, fresh_records, "{source:?}");
            } else {
                previous = Some((green, records));
            }
        }
    }
}

fn assert_use_composition_children(node: &SyntaxNode, start: u32, children: &[(SyntaxKind, &str)]) {
    let mut offset = start;
    let expected = children
        .iter()
        .map(|(kind, text)| {
            let range = offset..offset + text.len() as u32;
            offset = range.end;
            (*kind, range, text.to_string())
        })
        .collect::<Vec<_>>();
    assert_eq!(
        node.children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    u32::from(range.start())..u32::from(range.end()),
                    child.to_string(),
                )
            })
            .collect::<Vec<_>>(),
        expected,
        "{node:#?}"
    );
    assert_eq!(u32::from(node.text_range().start()), start);
    assert_eq!(u32::from(node.text_range().end()), offset);
}

#[test]
fn use_terminal_join_is_direct_tree_child() {
    use SyntaxKind::*;

    for (source, tree_text, expected) in [
        (
            "use p::{x}",
            "p::{x}",
            vec![(UsePath, "p"), (ColonColon, "::"), (UseGroup, "{x}")],
        ),
        (
            "use p::*",
            "p::*",
            vec![(UsePath, "p"), (ColonColon, "::"), (UseGlob, "*")],
        ),
        (
            "use p/{x}",
            "p/{x}",
            vec![(UsePath, "p"), (Slash, "/"), (UseGroup, "{x}")],
        ),
        (
            "use realm/p::{x}",
            "realm/p::{x}",
            vec![
                (RealmKw, "realm"),
                (Slash, "/"),
                (UsePath, "p"),
                (ColonColon, "::"),
                (UseGroup, "{x}"),
            ],
        ),
        (
            "use band::p::*",
            "band::p::*",
            vec![
                (BandKw, "band"),
                (ColonColon, "::"),
                (UsePath, "p"),
                (ColonColon, "::"),
                (UseGlob, "*"),
            ],
        ),
        (
            "use {p::{x}}",
            "p::{x}",
            vec![(UsePath, "p"), (ColonColon, "::"), (UseGroup, "{x}")],
        ),
        (
            "use q::* without {p::{x}}",
            "p::{x}",
            vec![(UsePath, "p"), (ColonColon, "::"), (UseGroup, "{x}")],
        ),
        (
            "use p::q/{x}",
            "p::q/{x}",
            vec![(UsePath, "p::q"), (Slash, "/"), (UseGroup, "{x}")],
        ),
    ] {
        let (green, records) = use_group_recoveries(source, None);
        assert!(records.is_empty(), "{source:?}");
        let root = SyntaxNode::new_root(green.clone());
        assert_eq!(root.text().to_string(), source);
        let tree = root
            .descendants()
            .find(|node| node.kind() == UseTree && node.text().to_string() == tree_text)
            .unwrap_or_else(|| panic!("missing tree {tree_text:?} in {source:?}: {root:#?}"));
        let start = source.find(tree_text).unwrap() as u32;
        let mut offset = start;
        let expected = expected
            .into_iter()
            .map(|(kind, text)| {
                let range = offset..offset + text.len() as u32;
                offset = range.end;
                (kind, range, text.to_owned())
            })
            .collect::<Vec<_>>();
        assert_eq!(
            tree.children_with_tokens()
                .map(|child| {
                    let range = child.text_range();
                    (
                        child.kind(),
                        u32::from(range.start())..u32::from(range.end()),
                        child.to_string(),
                    )
                })
                .collect::<Vec<_>>(),
            expected,
            "{source:?}"
        );
        let (frozen, frozen_records) = use_group_recoveries(source, Some(&records));
        assert_eq!(green, frozen, "{source:?}");
        assert_eq!(records, frozen_records, "{source:?}");
    }
}

fn use_group_recoveries(
    source: &str,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> (GreenNode, Vec<CommittedRecoveryRecord>) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = match frozen {
        Some(records) => Recover::reconcile_for_test(&operators, records),
        None => Recover::new_for_test(&operators),
    };
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let mut exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
    let Err(Either::Right(end)) = &mut exit else {
        panic!("complete use group must reach EOF: {source:?}")
    };
    emit_end(&mut builder, end);
    builder.finish_node();
    assert_eq!(input, "");
    (builder.finish(), recover.finish_recoveries_for_test())
}

#[test]
fn use_group_foreign_close_topology_and_unchanged_frozen_records() {
    use crate::recovery_record::*;
    use SyntaxKind::*;
    let close_role = |delimiter| GrammarRole::ClosingDelimiter {
        owner: ConstructRole::ImportGroup,
        delimiter,
    };
    let group_role = GrammarRole::Declaration(DeclarationRole::Import(ImportRole::GroupEntry));
    let close_expected =
        |delimiter| ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter));
    for (source, owner, children, occurrences) in [
        (
            "use {)}",
            UseGroup,
            vec![(LBrace, 4..5), (UseGroupForeignClose, 5..6), (RBrace, 6..7)],
            vec![(
                5..6,
                close_role(Delimiter::Brace),
                close_expected(Delimiter::Brace),
            )],
        ),
        (
            "use {@}",
            UseGroup,
            vec![(LBrace, 4..5), (Error, 5..6), (RBrace, 6..7)],
            vec![(5..6, group_role, ExpectedSyntax::Path)],
        ),
        (
            "use x::* without {)}",
            UseExclusionGroup,
            vec![
                (LBrace, 17..18),
                (UseGroupForeignClose, 18..19),
                (RBrace, 19..20),
            ],
            vec![(
                18..19,
                close_role(Delimiter::Brace),
                close_expected(Delimiter::Brace),
            )],
        ),
        (
            "use x::* without (})",
            UseExclusionGroup,
            vec![
                (LParen, 17..18),
                (UseGroupForeignClose, 18..19),
                (RParen, 19..20),
            ],
            vec![(
                18..19,
                close_role(Delimiter::Parenthesis),
                close_expected(Delimiter::Parenthesis),
            )],
        ),
        (
            "use {))}",
            UseGroup,
            vec![
                (LBrace, 4..5),
                (UseGroupForeignClose, 5..6),
                (UseGroupForeignClose, 6..7),
                (RBrace, 7..8),
            ],
            vec![
                (
                    5..6,
                    close_role(Delimiter::Brace),
                    close_expected(Delimiter::Brace),
                ),
                (
                    6..7,
                    close_role(Delimiter::Brace),
                    close_expected(Delimiter::Brace),
                ),
            ],
        ),
        (
            "use {)@}",
            UseGroup,
            vec![
                (LBrace, 4..5),
                (UseGroupForeignClose, 5..6),
                (Error, 6..7),
                (RBrace, 7..8),
            ],
            vec![
                (
                    5..6,
                    close_role(Delimiter::Brace),
                    close_expected(Delimiter::Brace),
                ),
                (6..7, group_role, ExpectedSyntax::Path),
            ],
        ),
        (
            "use {@)}",
            UseGroup,
            vec![(LBrace, 4..5), (Error, 5..6), (Error, 6..7), (RBrace, 7..8)],
            vec![(5..7, group_role, ExpectedSyntax::Path)],
        ),
        (
            "use {]}",
            UseGroup,
            vec![(LBrace, 4..5), (Error, 5..6), (RBrace, 6..7)],
            vec![(5..6, group_role, ExpectedSyntax::Path)],
        ),
        (
            "use { /*é*/ )}",
            UseGroup,
            vec![
                (LBrace, 4..5),
                (Whitespace, 5..6),
                (BlockComment, 6..12),
                (Whitespace, 12..13),
                (UseGroupForeignClose, 13..14),
                (RBrace, 14..15),
            ],
            vec![(
                13..14,
                close_role(Delimiter::Brace),
                close_expected(Delimiter::Brace),
            )],
        ),
    ] {
        let expected: Vec<_> = occurrences
            .into_iter()
            .enumerate()
            .map(|(id, (range, role, expected))| CommittedRecoveryRecord {
                id: DiagnosticId(id as u32),
                site: RecoverySiteKey {
                    role,
                    range: range.clone(),
                },
                kind: RecoveryKind::Error,
                unexpected: std::sync::Arc::from([UnexpectedSyntax::Token {
                    range: range.clone(),
                    category: UnexpectedCategory::OtherCharacter,
                }]),
                expectations: std::sync::Arc::from([SyntaxExpectation {
                    role,
                    expected,
                    range,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }]),
                primary_expectation: 0,
            })
            .collect();
        let (green, records) = use_group_recoveries(source, None);
        assert_eq!(records, expected, "{source:?}");
        let (frozen_green, frozen_records) = use_group_recoveries(source, Some(&records));
        assert_eq!(frozen_records, records, "{source:?}");
        assert_eq!(frozen_green, green, "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), source);
        let group = root
            .descendants()
            .find(|node| node.kind() == owner)
            .unwrap();
        assert_eq!(
            group
                .children_with_tokens()
                .map(|child| {
                    let range = child.text_range();
                    (
                        child.kind(),
                        u32::from(range.start())..u32::from(range.end()),
                    )
                })
                .collect::<Vec<_>>(),
            children,
            "{source:?}"
        );
        for child in group.children_with_tokens() {
            if child.kind() == UseGroupForeignClose {
                let wrapper = child.into_node().expect("foreign close is a node");
                let leaves: Vec<_> = wrapper.children_with_tokens().collect();
                assert_eq!(leaves.len(), 1, "{source:?}");
                let token = leaves[0]
                    .as_token()
                    .expect("foreign close contains a token leaf");
                assert_eq!(token.kind(), Error);
                assert_eq!(token.text_range(), wrapper.text_range());
                let range = token.text_range();
                assert_eq!(
                    token.text(),
                    &source[usize::from(range.start())..usize::from(range.end())]
                );
            } else if child.kind() == Error {
                assert!(
                    child.as_token().is_some(),
                    "direct group-entry Error is a token"
                );
            }
        }
    }
}

#[test]
fn use_group_accepted_groups_have_no_foreign_close_wrapper_or_records() {
    for source in [
        "use {}",
        "use {a,b}",
        "use x::* without {}",
        "use x::* without ()",
        "use {x::* without (a)}",
    ] {
        let (green, records) = use_group_recoveries(source, None);
        assert_eq!(green.to_string(), source);
        assert!(records.is_empty());
        let (frozen, frozen_records) = use_group_recoveries(source, Some(&records));
        assert_eq!(frozen, green);
        assert_eq!(frozen_records, records);
        assert_eq!(
            descendants_of_kind(
                &SyntaxNode::new_root(green),
                SyntaxKind::UseGroupForeignClose
            ),
            0
        );
    }
}

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

// Group children and OperatorName local closes have separate bounded matrices.
#[test]
fn use_schema_initial_operator_name_required_spelling() {
    use SyntaxKind::*;
    use rowan::TextRange;

    for (source, pending, leading, remainder) in [
        ("use (", None, "", ""),
        ("use ()", Some(")"), "", ""),
        ("use (foo", Some("foo"), "", ""),
        ("use ( +)", Some("+"), " ", ")"),
        ("use ( )", Some(")"), " ", ""),
        ("use (+)", None, "", ""),
    ] {
        let operators = OperatorTable::empty();
        let mut input = source;
        let mut recover = Recover::new_for_test(&operators);
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(Root.into());
        let mut exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
        if let Err(Either::Right(end)) = &mut exit {
            // EOF leading, if any, belongs to Root after the Statement.
            emit_end(&mut builder, end);
        }
        builder.finish_node();
        let root = SyntaxNode::new_root(finish_with_discarded_recoveries(builder, recover));
        let accepted = source == "use (+)";
        let end = if accepted { 7 } else { 5 };
        assert_eq!(input, remainder, "{source:?}");
        assert_eq!(root.to_string(), &source[..end], "{source:?}");
        let names: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == OperatorName)
            .collect();
        assert_eq!(names.len(), 1, "{source:?}");
        let name = &names[0];
        assert_eq!(
            name.text_range(),
            TextRange::new(4.into(), (end as u32).into())
        );
        assert_eq!(
            name.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
            [
                OperatorName,
                UsePath,
                UseTree,
                UseDeclaration,
                Statement,
                Root
            ]
        );
        let children: Vec<_> = name.children_with_tokens().collect();
        let expected = if accepted {
            vec![(LParen, 4..5), (Operator, 5..6), (RParen, 6..7)]
        } else {
            vec![(LParen, 4..5), (Missing, 5..5)]
        };
        assert_eq!(
            children
                .iter()
                .map(|child| {
                    let range = child.text_range();
                    (
                        child.kind(),
                        u32::from(range.start())..u32::from(range.end()),
                    )
                })
                .collect::<Vec<_>>(),
            expected,
            "{source:?}"
        );
        assert!(children[0].as_token().is_some());
        if accepted {
            assert!(children[1].as_token().is_some());
            assert!(children[2].as_token().is_some());
        } else {
            // Initial UseTree > UsePath and direct LParen, Missing select
            // Import(Path), expected OperatorName, primary alternative zero.
            // No admitted Operator means this is not the local Close slot.
            let missing = children[1].as_node().expect("direct spelling Missing");
            assert_eq!(missing.parent().as_ref(), Some(name));
            assert!(missing.children_with_tokens().next().is_none());
        }
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == Missing)
                .count(),
            usize::from(!accepted)
        );
        assert!(
            !root
                .descendants_with_tokens()
                .any(|child| matches!(child.kind(), Error | Invalid))
        );
        match (pending, exit) {
            (Some(spelling), Err(Either::Left(mut item))) => {
                assert_eq!(item.payload_view().spelling(), Some(spelling), "{source:?}");
                assert_eq!(emit_pending_leading_text(&mut item), leading, "{source:?}");
                assert_eq!(format!("{}{leading}{spelling}{input}", root), source);
            }
            (None, Err(Either::Right(_))) => {
                assert_eq!(root.to_string(), source);
                assert_eq!(
                    root.children_with_tokens()
                        .map(|child| child.kind())
                        .collect::<Vec<_>>(),
                    [Statement]
                );
            }
            _ => panic!("unexpected required-spelling handoff: {source:?}"),
        }
    }
}

#[test]
fn use_schema_nested_operator_name_required_spelling() {
    use SyntaxKind::*;

    for (source, group_children, missing_parents) in [
        (
            "use {(",
            vec![(LBrace, 4..5), (UseTree, 5..6), (Missing, 6..6)],
            vec![OperatorName, UseGroup],
        ),
        (
            "use {()}",
            vec![
                (LBrace, 4..5),
                (UseTree, 5..6),
                (UseGroupForeignClose, 6..7),
                (RBrace, 7..8),
            ],
            vec![OperatorName],
        ),
        (
            "use {(foo}",
            vec![
                (LBrace, 4..5),
                (UseTree, 5..6),
                (Missing, 6..6),
                (UseTree, 6..9),
                (RBrace, 9..10),
            ],
            vec![OperatorName, UseGroup],
        ),
        (
            "use {( ;next",
            vec![(LBrace, 4..5), (UseTree, 5..6), (Missing, 6..6)],
            vec![OperatorName, UseGroup],
        ),
        (
            "use {(+)}",
            vec![(LBrace, 4..5), (UseTree, 5..8), (RBrace, 8..9)],
            vec![],
        ),
    ] {
        let operators = OperatorTable::empty();
        let mut input = source;
        let mut recover = Recover::new_for_test(&operators);
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(Root.into());
        let mut exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
        if let Err(Either::Right(end)) = &mut exit {
            emit_end(&mut builder, end);
        }
        builder.finish_node();
        let root = SyntaxNode::new_root(finish_with_discarded_recoveries(builder, recover));
        let projection = |node: &SyntaxNode| {
            node.children_with_tokens()
                .map(|child| {
                    let range = child.text_range();
                    (
                        child.kind(),
                        u32::from(range.start())..u32::from(range.end()),
                    )
                })
                .collect::<Vec<_>>()
        };
        let names: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == OperatorName)
            .collect();
        assert_eq!(names.len(), 1, "{source:?}");
        let name = &names[0];
        assert_eq!(
            name.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
            [
                OperatorName,
                UsePath,
                UseTree,
                UseGroup,
                UseTree,
                UseDeclaration,
                Statement,
                Root
            ]
        );
        let accepted = missing_parents.is_empty();
        assert_eq!(
            projection(name),
            if accepted {
                vec![(LParen, 5..6), (Operator, 6..7), (RParen, 7..8)]
            } else {
                vec![(LParen, 5..6), (Missing, 6..6)]
            },
            "{source:?}"
        );
        let group = name
            .ancestors()
            .find(|node| node.kind() == UseGroup)
            .unwrap();
        assert_eq!(projection(&group), group_children, "{source:?}");
        for owner in [name, &group] {
            assert!(owner.children_with_tokens().all(|child| {
                child.as_node().is_some()
                    == matches!(child.kind(), Missing | UseTree | UseGroupForeignClose)
            }));
        }
        // Preorder keeps spelling separate from same-offset terminal Close or
        // Separator Missing; the following group child distinguishes those two.
        let missing: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect();
        assert_eq!(
            missing
                .iter()
                .map(|node| node.parent().unwrap().kind())
                .collect::<Vec<_>>(),
            missing_parents
        );
        for node in &missing {
            assert_eq!(node.text_range(), rowan::TextRange::empty(6.into()));
            assert!(node.children_with_tokens().next().is_none());
        }
        if missing.len() == 2 {
            assert_ne!(missing[0].parent(), missing[1].parent());
            assert_eq!(missing[0].parent().as_ref(), Some(name));
            assert_eq!(missing[1].parent().as_ref(), Some(&group));
        }
        let wrappers: Vec<_> = group
            .children()
            .filter(|node| node.kind() == UseGroupForeignClose)
            .collect();
        assert_eq!(wrappers.len(), usize::from(source == "use {()}"));
        for wrapper in wrappers {
            assert_eq!(projection(&wrapper), [(Error, 6..7)]);
            assert!(
                wrapper
                    .children_with_tokens()
                    .all(|child| child.as_token().is_some())
            );
        }
        assert!(
            !root
                .descendants_with_tokens()
                .any(|child| child.kind() == Invalid)
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|child| child.kind() == Error)
                .count(),
            usize::from(source == "use {()}")
        );
        if source == "use {( ;next" {
            assert_eq!(root.to_string(), "use {(");
            let Err(Either::Left(mut item)) = exit else {
                panic!("protected semicolon must remain pending")
            };
            assert_eq!(token_kind(&item), Some(TokenKind::Semicolon));
            assert_eq!(item.payload_view().spelling(), Some(";"));
            let extent = item.extent(source.len() - input.len());
            assert_eq!(extent.payload(), 7..8);
            assert_eq!(extent.leading(), 6..7);
            assert_eq!(emit_pending_leading_text(&mut item), " ");
            assert_eq!(input, "next");
            assert_eq!(format!("{root} ;{input}"), source);
        } else {
            assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
            assert_eq!(input, "");
            assert_eq!(root.to_string(), source);
        }
    }
}

#[test]
fn use_schema_exclusion_group_operator_name_required_spelling() {
    use SyntaxKind::*;

    for (open, close, foreign, opener, closer) in [
        ("{", "}", ")", LBrace, RBrace),
        ("(", ")", "}", LParen, RParen),
    ] {
        for (source, group_children, missing_parents) in [
            (
                format!("use a::* without {open}("),
                vec![(opener, 17..18), (UseTree, 18..19), (Missing, 19..19)],
                vec![OperatorName, UseExclusionGroup],
            ),
            (
                format!("use a::* without {open}({foreign}{close}"),
                vec![
                    (opener, 17..18),
                    (UseTree, 18..19),
                    (UseGroupForeignClose, 19..20),
                    (closer, 20..21),
                ],
                vec![OperatorName],
            ),
            (
                format!("use a::* without {open}(foo{close}"),
                vec![
                    (opener, 17..18),
                    (UseTree, 18..19),
                    (Missing, 19..19),
                    (UseTree, 19..22),
                    (closer, 22..23),
                ],
                vec![OperatorName, UseExclusionGroup],
            ),
            (
                format!("use a::* without {open}( ;next"),
                vec![(opener, 17..18), (UseTree, 18..19), (Missing, 19..19)],
                vec![OperatorName, UseExclusionGroup],
            ),
            (
                format!("use a::* without {open}(+){close}"),
                vec![(opener, 17..18), (UseTree, 18..21), (closer, 21..22)],
                vec![],
            ),
            (
                format!("use a::* without {open}({close}"),
                vec![(opener, 17..18), (UseTree, 18..19), (closer, 19..20)],
                vec![OperatorName],
            ),
        ] {
            let source = source.as_str();
            let operators = OperatorTable::empty();
            let mut input = source;
            let mut recover = Recover::new_for_test(&operators);
            let mut builder = GreenNodeBuilder::new();
            builder.start_node(Root.into());
            let mut exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
            if let Err(Either::Right(end)) = &mut exit {
                emit_end(&mut builder, end);
            }
            builder.finish_node();
            let root = SyntaxNode::new_root(finish_with_discarded_recoveries(builder, recover));
            let projection = |node: &SyntaxNode| {
                node.children_with_tokens()
                    .map(|child| {
                        let range = child.text_range();
                        (
                            child.kind(),
                            u32::from(range.start())..u32::from(range.end()),
                        )
                    })
                    .collect::<Vec<_>>()
            };
            let names: Vec<_> = root
                .descendants()
                .filter(|node| node.kind() == OperatorName)
                .collect();
            assert_eq!(names.len(), 1, "{source:?}");
            let name = &names[0];
            assert_eq!(
                name.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
                [
                    OperatorName,
                    UsePath,
                    UseTree,
                    UseExclusionGroup,
                    UseExclusion,
                    UseGlob,
                    UseTree,
                    UseDeclaration,
                    Statement,
                    Root
                ]
            );
            let accepted = missing_parents.is_empty();
            assert_eq!(
                projection(name),
                if accepted {
                    vec![(LParen, 18..19), (Operator, 19..20), (RParen, 20..21)]
                } else {
                    vec![(LParen, 18..19), (Missing, 19..19)]
                },
                "{source:?}"
            );
            let group = name
                .ancestors()
                .find(|node| node.kind() == UseExclusionGroup)
                .unwrap();
            assert_eq!(projection(&group), group_children, "{source:?}");
            for owner in [name, &group] {
                assert!(owner.children_with_tokens().all(|child| {
                    child.as_node().is_some()
                        == matches!(child.kind(), Missing | UseTree | UseGroupForeignClose)
                }));
            }
            // Preorder keeps spelling separate from same-offset terminal Close or
            // Separator Missing; the following group child distinguishes those two.
            let missing: Vec<_> = root
                .descendants()
                .filter(|node| node.kind() == Missing)
                .collect();
            assert_eq!(
                missing
                    .iter()
                    .map(|node| node.parent().unwrap().kind())
                    .collect::<Vec<_>>(),
                missing_parents
            );
            for node in &missing {
                assert_eq!(node.text_range(), rowan::TextRange::empty(19.into()));
                assert!(node.children_with_tokens().next().is_none());
            }
            if missing.len() == 2 {
                assert_ne!(missing[0].parent(), missing[1].parent());
                assert_eq!(missing[0].parent().as_ref(), Some(name));
                assert_eq!(missing[1].parent().as_ref(), Some(&group));
            }
            let wrappers: Vec<_> = group
                .children()
                .filter(|node| node.kind() == UseGroupForeignClose)
                .collect();
            assert_eq!(
                wrappers.len(),
                usize::from(source == format!("use a::* without {open}({foreign}{close}"))
            );
            for wrapper in wrappers {
                assert_eq!(projection(&wrapper), [(Error, 19..20)]);
                assert!(
                    wrapper
                        .children_with_tokens()
                        .all(|child| child.as_token().is_some())
                );
            }
            assert!(
                !root
                    .descendants_with_tokens()
                    .any(|child| child.kind() == Invalid)
            );
            assert_eq!(
                root.descendants_with_tokens()
                    .filter(|child| child.kind() == Error)
                    .count(),
                usize::from(source == format!("use a::* without {open}({foreign}{close}"))
            );
            if source == format!("use a::* without {open}( ;next") {
                assert_eq!(root.to_string(), format!("use a::* without {open}("));
                let Err(Either::Left(mut item)) = exit else {
                    panic!("protected semicolon must remain pending")
                };
                assert_eq!(token_kind(&item), Some(TokenKind::Semicolon));
                assert_eq!(item.payload_view().spelling(), Some(";"));
                let extent = item.extent(source.len() - input.len());
                assert_eq!(extent.payload(), 20..21);
                assert_eq!(extent.leading(), 19..20);
                assert_eq!(emit_pending_leading_text(&mut item), " ");
                assert_eq!(input, "next");
                assert_eq!(format!("{root} ;{input}"), source);
            } else {
                assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
                assert_eq!(input, "");
                assert_eq!(root.to_string(), source);
            }
        }
    }
}

#[test]
fn use_schema_operator_name_local_close_children() {
    use SyntaxKind::*;
    use rowan::TextRange;
    for (source, start, ancestors) in [
        (
            "use (+",
            4,
            vec![
                OperatorName,
                UsePath,
                UseTree,
                UseDeclaration,
                Statement,
                Root,
            ],
        ),
        (
            "use a::(+",
            7,
            vec![
                OperatorName,
                UsePath,
                UseTree,
                UseDeclaration,
                Statement,
                Root,
            ],
        ),
        (
            "use a::* without (+",
            17,
            vec![
                OperatorName,
                UseExclusion,
                UseGlob,
                UseTree,
                UseDeclaration,
                Statement,
                Root,
            ],
        ),
    ] {
        for closed in [false, true] {
            let source = format!("{source}{}", if closed { ")" } else { "" });
            let (green, _) = run_statement(&source);
            let root = SyntaxNode::new_root(green);
            assert_eq!(root.to_string(), source);
            let operators: Vec<_> = root
                .descendants()
                .filter(|node| node.kind() == OperatorName)
                .collect();
            assert_eq!(operators.len(), 1, "{source:?}");
            let operator = &operators[0];
            assert_eq!(
                operator
                    .ancestors()
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                ancestors,
                "{source:?}"
            );
            let end = start + 2 + u32::from(closed);
            assert_eq!(
                operator.text_range(),
                TextRange::new(start.into(), end.into())
            );
            let children: Vec<_> = operator.children_with_tokens().collect();
            assert_eq!(
                children
                    .iter()
                    .map(|child| (child.kind(), child.text_range()))
                    .collect::<Vec<_>>(),
                [
                    (LParen, TextRange::new(start.into(), (start + 1).into())),
                    (
                        Operator,
                        TextRange::new((start + 1).into(), (start + 2).into())
                    ),
                    (
                        if closed { RParen } else { Missing },
                        TextRange::new((start + 2).into(), end.into())
                    ),
                ],
                "{source:?}"
            );
            assert!(children[0].as_token().is_some());
            assert!(children[1].as_token().is_some());
            if closed {
                assert!(children[2].as_token().is_some());
            } else {
                // LParen + admitted Operator fixes this direct empty node's
                // expected syntax as the local closing parenthesis.
                let missing = children[2].as_node().expect("Missing is a node");
                assert_eq!(missing.parent().as_ref(), Some(operator));
                assert!(missing.children_with_tokens().next().is_none());
                assert!(missing.text_range().is_empty());
            }
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == Missing)
                    .count(),
                usize::from(!closed)
            );
            assert!(
                !root
                    .descendants_with_tokens()
                    .any(|child| matches!(child.kind(), Error | Invalid))
            );
        }
    }
}

#[test]
fn use_schema_operator_name_local_close_continuation() {
    use SyntaxKind::*;
    use rowan::TextRange;
    for (source, owner, expected) in [
        (
            "use (+::x",
            UsePath,
            vec![(OperatorName, 4..6), (ColonColon, 6..8), (Identifier, 8..9)],
        ),
        (
            "use (+ as x",
            UseTree,
            vec![(UsePath, 4..6), (Whitespace, 6..7), (UseAlias, 7..11)],
        ),
        (
            "use {(+}",
            UseGroup,
            vec![(LBrace, 4..5), (UseTree, 5..7), (RBrace, 7..8)],
        ),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        let caller = root
            .descendants()
            .find(|node| node.kind() == owner)
            .unwrap();
        assert_eq!(
            caller
                .children_with_tokens()
                .map(|child| {
                    let range = child.text_range();
                    (
                        child.kind(),
                        u32::from(range.start())..u32::from(range.end()),
                    )
                })
                .collect::<Vec<_>>(),
            expected,
            "{source:?}"
        );
        let operator = root
            .descendants()
            .find(|node| node.kind() == OperatorName)
            .unwrap();
        let start = if owner == UseGroup { 5 } else { 4 };
        assert_eq!(
            operator
                .children_with_tokens()
                .map(|child| (child.kind(), child.as_node().is_some()))
                .collect::<Vec<_>>(),
            [(LParen, false), (Operator, false), (Missing, true)]
        );
        let missing = operator.last_child().unwrap();
        assert_eq!(missing.text_range(), TextRange::empty((start + 2).into()));
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == Missing)
                .count(),
            1
        );
        assert!(
            !root
                .descendants_with_tokens()
                .any(|child| matches!(child.kind(), Error | Invalid))
        );
    }

    let (green, exit) = run_statement("use (+ )");
    assert_eq!(green.to_string(), "use (+");
    let root = SyntaxNode::new_root(green);
    let operator = root
        .descendants()
        .find(|node| node.kind() == OperatorName)
        .unwrap();
    assert_eq!(
        operator
            .children_with_tokens()
            .map(|child| child.kind())
            .collect::<Vec<_>>(),
        [LParen, Operator, Missing]
    );
    assert_eq!(
        operator.last_child().unwrap().text_range(),
        TextRange::empty(6.into())
    );
    assert!(
        !root
            .descendants_with_tokens()
            .any(|child| matches!(child.kind(), Error | Invalid))
    );
    let Some(Err(Either::Left(mut item))) = exit else {
        panic!("spaced close remains pending")
    };
    assert_eq!(token_kind(&item), Some(TokenKind::RParen));
    assert_eq!(
        emit_pending_leading_tokens(&mut item),
        [(Whitespace, " ".to_owned())]
    );
}

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
fn use_schema_glob_full_phase_composition() {
    use SyntaxKind::*;

    let projection = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    u32::from(range.start())..u32::from(range.end()),
                )
            })
            .collect::<Vec<_>>()
    };
    for (suffix, tail, pending) in [
        ("", vec![], None),
        (
            " as a as b",
            vec![
                (Whitespace, 8..9),
                (UseAlias, 9..13),
                (Whitespace, 13..14),
                (UseAlias, 14..18),
            ],
            None,
        ),
        (
            " without a",
            vec![
                (Whitespace, 8..9),
                (WithoutKw, 9..16),
                (Whitespace, 16..17),
                (UseExclusion, 17..18),
            ],
            None,
        ),
        (
            " without a, b, c",
            vec![
                (Whitespace, 8..9),
                (WithoutKw, 9..16),
                (Whitespace, 16..17),
                (UseExclusion, 17..18),
                (Comma, 18..19),
                (Whitespace, 19..20),
                (UseExclusion, 20..21),
                (Comma, 21..22),
                (Whitespace, 22..23),
                (UseExclusion, 23..24),
            ],
            None,
        ),
        (
            " as @ a without @ b",
            vec![
                (Whitespace, 8..9),
                (UseAlias, 9..15),
                (Whitespace, 15..16),
                (WithoutKw, 16..23),
                (Whitespace, 23..24),
                (Error, 24..25),
                (UseExclusion, 25..27),
            ],
            None,
        ),
        (" as", vec![(Whitespace, 8..9), (UseAlias, 9..11)], None),
        (
            " without",
            vec![(Whitespace, 8..9), (WithoutKw, 9..16), (Missing, 16..16)],
            None,
        ),
        (
            " without a,",
            vec![
                (Whitespace, 8..9),
                (WithoutKw, 9..16),
                (Whitespace, 16..17),
                (UseExclusion, 17..18),
                (Comma, 18..19),
                (Missing, 19..19),
            ],
            None,
        ),
        (
            " without a, @",
            vec![
                (Whitespace, 8..9),
                (WithoutKw, 9..16),
                (Whitespace, 16..17),
                (UseExclusion, 17..18),
                (Comma, 18..19),
                (Whitespace, 19..20),
                (Error, 20..21),
            ],
            None,
        ),
        (
            " without (+), {b}",
            vec![
                (Whitespace, 8..9),
                (WithoutKw, 9..16),
                (Whitespace, 16..17),
                (UseExclusion, 17..20),
                (Comma, 20..21),
                (Whitespace, 21..22),
                (UseExclusion, 22..25),
            ],
            None,
        ),
        (
            " without a v1 with anchor",
            vec![
                (Whitespace, 8..9),
                (WithoutKw, 9..16),
                (Whitespace, 16..17),
                (UseExclusion, 17..18),
            ],
            None,
        ),
        (
            " without a ;next",
            vec![
                (Whitespace, 8..9),
                (WithoutKw, 9..16),
                (Whitespace, 16..17),
                (UseExclusion, 17..18),
            ],
            Some((18, 18..19, 19..20)),
        ),
        (
            " without @ a ;next",
            vec![
                (Whitespace, 8..9),
                (WithoutKw, 9..16),
                (Whitespace, 16..17),
                (Error, 17..18),
                (UseExclusion, 18..20),
            ],
            Some((20, 20..21, 21..22)),
        ),
    ] {
        let source = format!("use p::*{suffix}");
        let operators = OperatorTable::empty();
        let mut input = source.as_str();
        let mut recover = Recover::new_for_test(&operators);
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(Root.into());
        let mut exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
        if let Err(Either::Right(end)) = &mut exit {
            emit_end(&mut builder, end);
        }
        builder.finish_node();
        let root = SyntaxNode::new_root(finish_with_discarded_recoveries(builder, recover));
        let tree = root
            .descendants()
            .find(|node| node.kind() == UseTree)
            .unwrap();
        let qualifier = suffix == " without a v1 with anchor";
        let end = pending.as_ref().map_or(source.len(), |(end, _, _)| *end) as u32;
        let glob_end = if qualifier { 18 } else { end };
        let mut tree_children = vec![(UsePath, 4..5), (ColonColon, 5..7), (UseGlob, 7..glob_end)];
        if qualifier {
            tree_children.push((UseQualifiers, 18..33));
        }
        assert_eq!(projection(&tree), tree_children, "{source:?}");
        let path = tree.children().next().unwrap();
        assert_eq!(projection(&path), [(Identifier, 4..5)]);
        let glob = tree.children().find(|node| node.kind() == UseGlob).unwrap();
        assert_eq!(
            glob.ancestors()
                .take(4)
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [UseGlob, UseTree, UseDeclaration, Statement]
        );
        let mut expected = vec![(Star, 7..8)];
        expected.extend(tail);
        assert_eq!(projection(&glob), expected);
        // Each component supplies its own ordered recovery slots. In particular,
        // alias Error is not merged into the later direct required-exclusion Error.
        let mut owners = vec![(glob.clone(), expected)];
        for child in glob.children() {
            let range = child.text_range();
            let start = u32::from(range.start());
            let end = u32::from(range.end());
            let children = match (child.kind(), start, end) {
                (UseAlias, 9, 13) => {
                    vec![(AsKw, 9..11), (Whitespace, 11..12), (Identifier, 12..13)]
                }
                (UseAlias, 14, 18) => {
                    vec![(AsKw, 14..16), (Whitespace, 16..17), (Identifier, 17..18)]
                }
                (UseAlias, 9, 15) => vec![
                    (AsKw, 9..11),
                    (Whitespace, 11..12),
                    (Error, 12..13),
                    (Whitespace, 13..14),
                    (Identifier, 14..15),
                ],
                (UseAlias, 9, 11) => vec![(AsKw, 9..11), (Missing, 11..11)],
                (UseExclusion, 25, 27) => vec![(Whitespace, 25..26), (Identifier, 26..27)],
                (UseExclusion, 18, 20) => vec![(Whitespace, 18..19), (Identifier, 19..20)],
                (UseExclusion, 17, 20) => vec![(OperatorName, 17..20)],
                (UseExclusion, 22, 25) => vec![(UseExclusionGroup, 22..25)],
                (UseExclusion, _, _) => vec![(Identifier, start..end)],
                (Missing, _, _) => continue,
                _ => panic!("unexpected Glob component in {source:?}"),
            };
            assert_eq!(
                child
                    .ancestors()
                    .take(5)
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                [child.kind(), UseGlob, UseTree, UseDeclaration, Statement]
            );
            assert_eq!(projection(&child), children);
            if let Some(name) = child.children().find(|node| node.kind() == OperatorName) {
                assert_eq!(
                    projection(&name),
                    [(LParen, 17..18), (Operator, 18..19), (RParen, 19..20)]
                );
            }
            if let Some(group) = child
                .children()
                .find(|node| node.kind() == UseExclusionGroup)
            {
                assert_eq!(
                    projection(&group),
                    [(LBrace, 22..23), (UseTree, 23..24), (RBrace, 24..25)]
                );
                let item = group.children().next().unwrap();
                assert_eq!(projection(&item), [(UsePath, 23..24)]);
                assert_eq!(
                    projection(&item.children().next().unwrap()),
                    [(Identifier, 23..24)]
                );
            }
            owners.push((child, children));
        }
        let mut expected_recoveries = Vec::new();
        for (owner, children) in &owners {
            let mut runs = Vec::new();
            let mut current: Option<std::ops::Range<u32>> = None;
            for child in owner.children_with_tokens() {
                let range = child.text_range();
                if child.kind() == Error {
                    if let Some(run) = &mut current {
                        assert_eq!(run.end, u32::from(range.start()));
                        run.end = u32::from(range.end());
                    } else {
                        current = Some(u32::from(range.start())..u32::from(range.end()));
                    }
                } else if let Some(run) = current.take() {
                    runs.push(run);
                }
            }
            if let Some(run) = current {
                runs.push(run);
            }
            assert_eq!(
                runs,
                children
                    .iter()
                    .filter(|(kind, _)| *kind == Error)
                    .map(|(_, range)| range.clone())
                    .collect::<Vec<_>>()
            );
            for (kind, range) in children
                .iter()
                .filter(|(kind, _)| matches!(kind, Missing | Error))
            {
                expected_recoveries.push((owner.clone(), *kind, range.clone()));
            }
        }
        let recoveries: Vec<_> = root
            .descendants_with_tokens()
            .filter(|child| matches!(child.kind(), Error | Missing))
            .collect();
        assert_eq!(recoveries.len(), expected_recoveries.len());
        for (owner, kind, range) in expected_recoveries {
            let matches: Vec<_> = recoveries
                .iter()
                .filter(|child| {
                    child.parent().as_ref() == Some(&owner)
                        && child.kind() == kind
                        && child.text_range()
                            == rowan::TextRange::new(range.start.into(), range.end.into())
                })
                .collect();
            assert_eq!(matches.len(), 1);
            if let Some(missing) = matches[0].as_node() {
                assert!(missing.text_range().is_empty());
                assert!(missing.children_with_tokens().next().is_none());
            }
        }
        if qualifier {
            let qualifiers = tree
                .children()
                .find(|node| node.kind() == UseQualifiers)
                .unwrap();
            assert_eq!(
                projection(&qualifiers),
                [
                    (Whitespace, 18..19),
                    (UseVersion, 19..21),
                    (Whitespace, 21..22),
                    (UseAnchor, 22..33)
                ]
            );
            let version = qualifiers.children().next().unwrap();
            assert_eq!(projection(&version), [(Version, 19..21)]);
            let anchor = qualifiers
                .children()
                .find(|node| node.kind() == UseAnchor)
                .unwrap();
            assert_eq!(projection(&anchor), [(WithKw, 22..26), (UsePath, 26..33)]);
            assert_eq!(
                projection(&anchor.children().next().unwrap()),
                [(Whitespace, 26..27), (Identifier, 27..33)]
            );
        }
        for node in root.descendants() {
            for child in node.children_with_tokens() {
                assert_eq!(child.parent().as_ref(), Some(&node));
                assert_eq!(
                    child.as_node().is_some(),
                    matches!(
                        child.kind(),
                        Statement
                            | UseDeclaration
                            | UseTree
                            | UsePath
                            | UseGlob
                            | UseAlias
                            | UseExclusion
                            | UseExclusionGroup
                            | OperatorName
                            | UseQualifiers
                            | UseVersion
                            | UseAnchor
                            | Missing
                    )
                );
            }
        }
        for child in root.descendants_with_tokens() {
            let range = child.text_range();
            assert_eq!(
                child.to_string(),
                source[usize::from(range.start())..usize::from(range.end())]
            );
            assert!(!matches!(child.kind(), Invalid | UseGroupForeignClose));
        }
        if let Some((end, leading, payload)) = pending {
            assert_eq!(root.to_string(), source[..end]);
            let Err(Either::Left(mut item)) = exit else {
                panic!("protected semicolon must remain pending")
            };
            assert_eq!(token_kind(&item), Some(TokenKind::Semicolon));
            assert_eq!(item.payload_view().spelling(), Some(";"));
            let extent = item.extent(source.len() - input.len());
            assert_eq!(extent.leading(), leading.clone());
            assert_eq!(extent.payload(), payload);
            let leading_text = emit_pending_leading_text(&mut item);
            assert_eq!(leading_text, source[leading]);
            assert_eq!(input, "next");
            assert_eq!(format!("{root}{leading_text};{input}"), source);
        } else {
            assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
            assert_eq!(input, "");
            assert_eq!(root.to_string(), source);
        }
    }
}

#[test]
fn use_schema_glob_band_caller_qualifier_closure() {
    use SyntaxKind::*;

    let projection = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    u32::from(range.start())..u32::from(range.end()),
                )
            })
            .collect::<Vec<_>>()
    };
    for (source, glob_end, end, glob_children) in [
        (
            "use band::* as a as b v1 with anchor",
            21,
            36,
            vec![
                (Star, 10..11),
                (Whitespace, 11..12),
                (UseAlias, 12..16),
                (Whitespace, 16..17),
                (UseAlias, 17..21),
            ],
        ),
        (
            "use band::* as a without b, c v1 with anchor",
            29,
            44,
            vec![
                (Star, 10..11),
                (Whitespace, 11..12),
                (UseAlias, 12..16),
                (Whitespace, 16..17),
                (WithoutKw, 17..24),
                (Whitespace, 24..25),
                (UseExclusion, 25..26),
                (Comma, 26..27),
                (Whitespace, 27..28),
                (UseExclusion, 28..29),
            ],
        ),
    ] {
        let (green, exit) = run_statement(source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green);
        let tree = root
            .descendants()
            .find(|node| node.kind() == UseTree)
            .unwrap();
        assert_eq!(
            projection(&tree),
            [
                (BandKw, 4..8),
                (ColonColon, 8..10),
                (UseGlob, 10..glob_end),
                (UseQualifiers, glob_end..end)
            ]
        );
        let glob = tree.children().find(|node| node.kind() == UseGlob).unwrap();
        let qualifiers = tree
            .children()
            .find(|node| node.kind() == UseQualifiers)
            .unwrap();
        for node in [&glob, &qualifiers] {
            assert_eq!(
                node.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
                [node.kind(), UseTree, UseDeclaration, Statement, Root]
            );
        }
        assert_eq!(projection(&glob), glob_children);
        for child in glob.children() {
            assert_eq!(
                child
                    .ancestors()
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                [
                    child.kind(),
                    UseGlob,
                    UseTree,
                    UseDeclaration,
                    Statement,
                    Root
                ]
            );
            let start = u32::from(child.text_range().start());
            if child.kind() == UseAlias {
                assert_eq!(
                    projection(&child),
                    [
                        (AsKw, start..start + 2),
                        (Whitespace, start + 2..start + 3),
                        (Identifier, start + 3..start + 4)
                    ]
                );
            } else {
                assert_eq!(child.kind(), UseExclusion);
                assert_eq!(projection(&child), [(Identifier, start..start + 1)]);
            }
        }
        assert_eq!(
            projection(&qualifiers),
            [
                (Whitespace, glob_end..glob_end + 1),
                (UseVersion, glob_end + 1..glob_end + 3),
                (Whitespace, glob_end + 3..glob_end + 4),
                (UseAnchor, glob_end + 4..end)
            ]
        );
        let version = qualifiers.children().next().unwrap();
        assert_eq!(
            projection(&version),
            [(Version, glob_end + 1..glob_end + 3)]
        );
        let anchor = qualifiers
            .children()
            .find(|node| node.kind() == UseAnchor)
            .unwrap();
        assert_eq!(
            projection(&anchor),
            [
                (WithKw, glob_end + 4..glob_end + 8),
                (UsePath, glob_end + 8..end)
            ]
        );
        let path = anchor.children().next().unwrap();
        assert_eq!(
            projection(&path),
            [
                (Whitespace, glob_end + 8..glob_end + 9),
                (Identifier, glob_end + 9..end)
            ]
        );
        for node in root.descendants() {
            for child in node.children_with_tokens() {
                assert_eq!(child.parent().as_ref(), Some(&node));
                assert_eq!(
                    child.as_node().is_some(),
                    matches!(
                        child.kind(),
                        Statement
                            | UseDeclaration
                            | UseTree
                            | UseGlob
                            | UseAlias
                            | UseExclusion
                            | UseQualifiers
                            | UseVersion
                            | UseAnchor
                            | UsePath
                    )
                );
            }
        }
        for child in root.descendants_with_tokens() {
            let range = child.text_range();
            assert_eq!(
                child.to_string(),
                source[usize::from(range.start())..usize::from(range.end())]
            );
            assert!(!matches!(
                child.kind(),
                Missing | Error | Invalid | UseGroupForeignClose
            ));
        }
    }
}

#[test]
fn use_schema_mod_form_head_leading_ownership() {
    use SyntaxKind::*;

    let projection = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    u32::from(range.start())..u32::from(range.end()),
                )
            })
            .collect::<Vec<_>>()
    };
    for (source, tree_children, path_children, pending) in [
        (
            "use mod target",
            vec![(ModKw, 4..7), (Whitespace, 7..8), (UsePath, 8..14)],
            vec![(Identifier, 8..14)],
            None,
        ),
        (
            "use mod /*é*/ target",
            vec![
                (ModKw, 4..7),
                (Whitespace, 7..8),
                (BlockComment, 8..14),
                (Whitespace, 14..15),
                (UsePath, 15..21),
            ],
            vec![(Identifier, 15..21)],
            None,
        ),
        (
            "use mod",
            vec![(ModKw, 4..7), (UsePath, 7..7)],
            vec![(Missing, 7..7)],
            None,
        ),
        (
            "use mod @",
            vec![(ModKw, 4..7), (UsePath, 7..9)],
            vec![(Whitespace, 7..8), (Error, 8..9)],
            None,
        ),
        (
            "use mod @ /*é*/ target",
            vec![(ModKw, 4..7), (UsePath, 7..23)],
            vec![
                (Whitespace, 7..8),
                (Error, 8..9),
                (Whitespace, 9..10),
                (BlockComment, 10..16),
                (Whitespace, 16..17),
                (Identifier, 17..23),
            ],
            None,
        ),
        (
            "use mod ;next",
            vec![(ModKw, 4..7), (UsePath, 7..7)],
            vec![(Missing, 7..7)],
            Some((7, 7..8, 8..9, ";", "next")),
        ),
        (
            "use mod as",
            vec![(ModKw, 4..7), (UsePath, 7..8)],
            vec![(Whitespace, 7..8), (Missing, 8..8)],
            Some((8, 7..8, 8..10, "as", "")),
        ),
        (
            "use mod target::{x}",
            vec![
                (ModKw, 4..7),
                (Whitespace, 7..8),
                (UsePath, 8..14),
                (ColonColon, 14..16),
                (UseGroup, 16..19),
            ],
            vec![(Identifier, 8..14)],
            None,
        ),
        (
            "use mod target::*",
            vec![
                (ModKw, 4..7),
                (Whitespace, 7..8),
                (UsePath, 8..14),
                (ColonColon, 14..16),
                (UseGlob, 16..17),
            ],
            vec![(Identifier, 8..14)],
            None,
        ),
        (
            "use mod target::(+)",
            vec![(ModKw, 4..7), (Whitespace, 7..8), (UsePath, 8..19)],
            vec![
                (Identifier, 8..14),
                (ColonColon, 14..16),
                (OperatorName, 16..19),
            ],
            None,
        ),
    ] {
        let operators = OperatorTable::empty();
        let mut input = source;
        let mut recover = Recover::new_for_test(&operators);
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(Root.into());
        let mut exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
        if let Err(Either::Right(end)) = &mut exit {
            emit_end(&mut builder, end);
        }
        builder.finish_node();
        let root = SyntaxNode::new_root(finish_with_discarded_recoveries(builder, recover));
        let tree = root
            .descendants()
            .find(|node| node.kind() == UseTree)
            .unwrap();
        assert_eq!(projection(&tree), tree_children, "{source:?}");
        let path = tree.children().find(|node| node.kind() == UsePath).unwrap();
        assert_eq!(
            path.ancestors()
                .take(4)
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [UsePath, UseTree, UseDeclaration, Statement]
        );
        assert_eq!(projection(&path), path_children);
        if let Some(group) = tree.children().find(|node| node.kind() == UseGroup) {
            assert_eq!(
                projection(&group),
                [(LBrace, 16..17), (UseTree, 17..18), (RBrace, 18..19)]
            );
            let item = group.children().next().unwrap();
            assert_eq!(projection(&item), [(UsePath, 17..18)]);
            assert_eq!(
                projection(&item.children().next().unwrap()),
                [(Identifier, 17..18)]
            );
        }
        if let Some(glob) = tree.children().find(|node| node.kind() == UseGlob) {
            assert_eq!(projection(&glob), [(Star, 16..17)]);
        }
        if let Some(name) = path.children().find(|node| node.kind() == OperatorName) {
            assert_eq!(
                projection(&name),
                [(LParen, 16..17), (Operator, 17..18), (RParen, 18..19)]
            );
        }
        let mut runs = Vec::new();
        let mut current: Option<std::ops::Range<u32>> = None;
        for child in path.children_with_tokens() {
            let range = child.text_range();
            // Group malformed leaves only by direct adjacency, never spelling.
            if child.kind() == Error {
                if let Some(run) = &mut current {
                    assert_eq!(run.end, u32::from(range.start()));
                    run.end = u32::from(range.end());
                } else {
                    current = Some(u32::from(range.start())..u32::from(range.end()));
                }
            } else if let Some(run) = current.take() {
                runs.push(run);
            }
        }
        if let Some(run) = current {
            runs.push(run);
        }
        assert_eq!(
            runs,
            path_children
                .iter()
                .filter(|(kind, _)| *kind == Error)
                .map(|(_, range)| range.clone())
                .collect::<Vec<_>>()
        );
        let recoveries: Vec<_> = root
            .descendants_with_tokens()
            .filter(|child| matches!(child.kind(), Error | Missing))
            .collect();
        let expected: Vec<_> = path_children
            .iter()
            .filter(|(kind, _)| matches!(kind, Error | Missing))
            .collect();
        assert_eq!(recoveries.len(), expected.len());
        for (child, (kind, range)) in recoveries.iter().zip(expected) {
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.parent().as_ref(), Some(&path));
            assert_eq!(
                child.text_range(),
                rowan::TextRange::new(range.start.into(), range.end.into())
            );
            if let Some(missing) = child.as_node() {
                assert!(missing.text_range().is_empty());
                assert!(missing.children_with_tokens().next().is_none());
            }
        }
        for node in root.descendants() {
            for child in node.children_with_tokens() {
                assert_eq!(child.parent().as_ref(), Some(&node));
                assert_eq!(
                    child.as_node().is_some(),
                    matches!(
                        child.kind(),
                        Statement
                            | UseDeclaration
                            | UseTree
                            | UsePath
                            | UseGroup
                            | UseGlob
                            | OperatorName
                            | Missing
                    )
                );
            }
        }
        for child in root.descendants_with_tokens() {
            let range = child.text_range();
            assert_eq!(
                child.to_string(),
                source[usize::from(range.start())..usize::from(range.end())]
            );
            assert!(!matches!(child.kind(), Invalid | UseGroupForeignClose));
        }
        if let Some((end, leading, payload, spelling, remainder)) = pending {
            assert_eq!(root.to_string(), source[..end]);
            let Err(Either::Left(mut item)) = exit else {
                panic!("boundary Item must remain pending")
            };
            let extent = item.extent(source.len() - input.len());
            assert_eq!(extent.leading(), leading);
            assert_eq!(extent.payload(), payload.clone());
            assert_eq!(item.payload_view().spelling(), Some(spelling));
            assert_eq!(input, remainder);
            let leading_text = emit_pending_leading_text(&mut item);
            assert_eq!(leading_text, source[end..payload.start]);
            assert_eq!(format!("{root}{leading_text}{spelling}{input}"), source);
        } else {
            assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
            assert_eq!(input, "");
            assert_eq!(root.to_string(), source);
        }
    }
    let source = "use {mod target}";
    assert_use_schema_children(
        source,
        UseGroup,
        &[UseGroup, UseTree, UseDeclaration, Statement],
        &[(LBrace, 4..5), (UseTree, 5..15), (RBrace, 15..16)],
    );
    assert_use_schema_occurrence(
        source,
        UseTree,
        1,
        &[UseTree, UseGroup, UseTree, UseDeclaration, Statement],
        &[(ModKw, 5..8), (Whitespace, 8..9), (UsePath, 9..15)],
    );
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let root = SyntaxNode::new_root(green);
    let path = root
        .descendants()
        .find(|node| node.kind() == UsePath)
        .unwrap();
    assert_eq!(projection(&path), [(Identifier, 9..15)]);
    assert_eq!(
        path.ancestors()
            .take(6)
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [
            UsePath,
            UseTree,
            UseGroup,
            UseTree,
            UseDeclaration,
            Statement
        ]
    );
    assert!(
        !root
            .descendants_with_tokens()
            .any(|child| matches!(child.kind(), Error | Missing | Invalid))
    );
}

#[test]
fn use_schema_marker_target_dispatch() {
    use SyntaxKind::*;

    let projection = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    u32::from(range.start())..u32::from(range.end()),
                )
            })
            .collect::<Vec<_>>()
    };
    let assert_source = |root: &SyntaxNode, source: &str| {
        for child in root.descendants_with_tokens() {
            let range = child.text_range();
            assert_eq!(
                child.to_string(),
                source[usize::from(range.start())..usize::from(range.end())]
            );
            assert!(!matches!(
                child.kind(),
                Invalid | UseExclusion | UseExclusionGroup | UseGroupForeignClose
            ));
        }
        for node in root.descendants() {
            for child in node.children_with_tokens() {
                assert_eq!(child.parent().as_ref(), Some(&node));
                assert_eq!(
                    child.as_node().is_some(),
                    matches!(
                        child.kind(),
                        Statement
                            | UseDeclaration
                            | UseTree
                            | UsePath
                            | UseGroup
                            | UseGlob
                            | OperatorName
                            | Missing
                    )
                );
            }
        }
    };
    for (marker, marker_kind, marker_end, separator_kind) in [
        ("realm/", RealmKw, 9, Slash),
        ("band::", BandKw, 8, ColonColon),
    ] {
        for (text, target_kind, children, recovery, pending) in [
            (
                "{a}",
                UseGroup,
                vec![(LBrace, 10..11), (UseTree, 11..12), (RBrace, 12..13)],
                None,
                false,
            ),
            ("name", UsePath, vec![(Identifier, 10..14)], None, false),
            (
                "",
                UsePath,
                vec![(Missing, 10..10)],
                Some((Missing, UsePath, 10..10)),
                false,
            ),
            (
                "@",
                UsePath,
                vec![(Error, 10..11)],
                Some((Error, UsePath, 10..11)),
                false,
            ),
            (
                "@ name",
                UsePath,
                vec![(Error, 10..11), (Whitespace, 11..12), (Identifier, 12..16)],
                Some((Error, UsePath, 10..11)),
                false,
            ),
            ("(+)", UsePath, vec![(OperatorName, 10..13)], None, false),
            (
                "(+",
                UsePath,
                vec![(OperatorName, 10..12)],
                Some((Missing, OperatorName, 12..12)),
                false,
            ),
            (
                "()",
                UsePath,
                vec![(Error, 10..11)],
                Some((Error, UsePath, 10..11)),
                true,
            ),
        ] {
            let source = format!("use {marker}{text}");
            let operators = OperatorTable::empty();
            let mut input = source.as_str();
            let mut recover = Recover::new_for_test(&operators);
            let mut builder = GreenNodeBuilder::new();
            builder.start_node(Root.into());
            let mut exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
            if let Err(Either::Right(end)) = &mut exit {
                emit_end(&mut builder, end);
            }
            builder.finish_node();
            let root = SyntaxNode::new_root(finish_with_discarded_recoveries(builder, recover));
            let end = if pending { 11 } else { source.len() as u32 };
            let tree = root
                .descendants()
                .find(|node| node.kind() == UseTree)
                .unwrap();
            assert_eq!(
                projection(&tree),
                [
                    (marker_kind, 4..marker_end),
                    (separator_kind, marker_end..10),
                    (target_kind, 10..end)
                ],
                "{source:?}"
            );
            let target = tree.children().next().unwrap();
            assert_eq!(
                target
                    .ancestors()
                    .take(4)
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                [target_kind, UseTree, UseDeclaration, Statement]
            );
            assert_eq!(projection(&target), children);
            if target_kind == UseGroup {
                let item = target.children().next().unwrap();
                assert_eq!(projection(&item), [(UsePath, 11..12)]);
                assert_eq!(
                    projection(&item.children().next().unwrap()),
                    [(Identifier, 11..12)]
                );
            }
            let names: Vec<_> = target
                .descendants()
                .filter(|node| node.kind() == OperatorName)
                .collect();
            assert_eq!(names.len(), usize::from(matches!(text, "(+)" | "(+")));
            if let Some(name) = names.first() {
                assert_eq!(
                    name.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
                    [
                        OperatorName,
                        UsePath,
                        UseTree,
                        UseDeclaration,
                        Statement,
                        Root
                    ]
                );
                let close = if text == "(+)" {
                    (RParen, 12..13)
                } else {
                    (Missing, 12..12)
                };
                assert_eq!(
                    projection(name),
                    [(LParen, 10..11), (Operator, 11..12), close]
                );
            }
            let recoveries: Vec<_> = root
                .descendants_with_tokens()
                .filter(|child| matches!(child.kind(), Missing | Error))
                .collect();
            assert_eq!(recoveries.len(), usize::from(recovery.is_some()));
            if let Some((kind, owner, range)) = recovery {
                let child = &recoveries[0];
                assert_eq!(child.kind(), kind);
                assert_eq!(child.parent().unwrap().kind(), owner);
                assert_eq!(
                    child.text_range(),
                    rowan::TextRange::new(range.start.into(), range.end.into())
                );
                if let Some(node) = child.as_node() {
                    assert!(node.text_range().is_empty());
                    assert!(node.children_with_tokens().next().is_none());
                }
            }
            let mut runs = Vec::new();
            let mut current: Option<std::ops::Range<u32>> = None;
            for child in target.children_with_tokens() {
                let range = child.text_range();
                // The direct owner and adjacency select Error, not its spelling.
                if child.kind() == Error {
                    if let Some(run) = &mut current {
                        assert_eq!(run.end, u32::from(range.start()));
                        run.end = u32::from(range.end());
                    } else {
                        current = Some(u32::from(range.start())..u32::from(range.end()));
                    }
                } else if let Some(run) = current.take() {
                    runs.push(run);
                }
            }
            if let Some(run) = current {
                runs.push(run);
            }
            assert_eq!(
                runs,
                children
                    .iter()
                    .filter(|(kind, _)| *kind == Error)
                    .map(|(_, range)| range.clone())
                    .collect::<Vec<_>>()
            );
            assert_source(&root, &source);
            if pending {
                assert_eq!(root.to_string(), source[..11]);
                let Err(Either::Left(mut item)) = exit else {
                    panic!("RParen must remain pending")
                };
                assert_eq!(token_kind(&item), Some(TokenKind::RParen));
                assert_eq!(item.payload_view().spelling(), Some(")"));
                let extent = item.extent(source.len() - input.len());
                assert_eq!(extent.leading(), 11..11);
                assert_eq!(extent.payload(), 11..12);
                assert_eq!(emit_pending_leading_text(&mut item), "");
                assert_eq!(input, "");
                assert_eq!(format!("{root}){input}"), source);
            } else {
                assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
                assert_eq!(input, "");
                assert_eq!(root.to_string(), source);
            }
        }
    }
    // The shared dispatcher is witnessed only where lexically reachable:
    // adjacent realm/* starts a comment, so the direct glob control is Band-only.
    let source = "use band::*";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let root = SyntaxNode::new_root(green);
    let tree = root
        .descendants()
        .find(|node| node.kind() == UseTree)
        .unwrap();
    assert_eq!(
        tree.text_range(),
        rowan::TextRange::new(4.into(), 11.into())
    );
    assert_eq!(
        projection(&tree),
        [(BandKw, 4..8), (ColonColon, 8..10), (UseGlob, 10..11)]
    );
    let glob = tree.children().next().unwrap();
    assert_eq!(projection(&glob), [(Star, 10..11)]);
    assert_eq!(
        glob.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
        [UseGlob, UseTree, UseDeclaration, Statement, Root]
    );
    assert!(
        !root
            .descendants_with_tokens()
            .any(|child| matches!(child.kind(), Missing | Error))
    );
    assert_source(&root, source);

    for (source, children) in [
        ("use realm", vec![(Identifier, 4..9)]),
        ("use band", vec![(Identifier, 4..8)]),
        (
            "use realm::name",
            vec![
                (Identifier, 4..9),
                (ColonColon, 9..11),
                (Identifier, 11..15),
            ],
        ),
        (
            "use band/name",
            vec![(Identifier, 4..8), (Slash, 8..9), (Identifier, 9..13)],
        ),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green);
        let tree = root
            .descendants()
            .find(|node| node.kind() == UseTree)
            .unwrap();
        assert_eq!(projection(&tree), [(UsePath, 4..source.len() as u32)]);
        assert_eq!(projection(&tree.children().next().unwrap()), children);
        assert!(
            !root
                .descendants_with_tokens()
                .any(|child| matches!(child.kind(), RealmKw | BandKw | Missing | Error))
        );
        assert_source(&root, source);
    }
    let source = "use realm/{band::name}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let root = SyntaxNode::new_root(green);
    let trees: Vec<_> = root
        .descendants()
        .filter(|node| node.kind() == UseTree)
        .collect();
    assert_eq!(trees.len(), 2);
    assert_eq!(
        projection(&trees[0]),
        [(RealmKw, 4..9), (Slash, 9..10), (UseGroup, 10..22)]
    );
    let group = trees[0].children().next().unwrap();
    assert_eq!(
        projection(&group),
        [(LBrace, 10..11), (UseTree, 11..21), (RBrace, 21..22)]
    );
    assert_eq!(
        projection(&trees[1]),
        [(BandKw, 11..15), (ColonColon, 15..17), (UsePath, 17..21)]
    );
    let path = trees[1].children().next().unwrap();
    assert_eq!(
        path.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            UsePath,
            UseTree,
            UseGroup,
            UseTree,
            UseDeclaration,
            Statement,
            Root
        ]
    );
    assert_eq!(projection(&path), [(Identifier, 17..21)]);
    assert!(
        !root
            .descendants_with_tokens()
            .any(|child| matches!(child.kind(), Missing | Error))
    );
    assert_source(&root, source);
}

#[test]
fn use_schema_qualifier_anchor_path_ownership() {
    use SyntaxKind::*;

    let projection = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    u32::from(range.start())..u32::from(range.end()),
                )
            })
            .collect::<Vec<_>>()
    };
    // Fresh Missing expects Path, post-separator Missing expects Identifier,
    // and raw Error expects Path. This evidence selects only Rowan topology;
    // neither recovery records nor opaque Error spelling select an occurrence.
    for (source, version, anchor_start, path_children, pending) in [
        ("use a v1", true, None, vec![], None),
        (
            "use a with target",
            false,
            Some(6),
            vec![(Whitespace, 10..11), (Identifier, 11..17)],
            None,
        ),
        (
            "use a v1 with target",
            true,
            Some(9),
            vec![(Whitespace, 13..14), (Identifier, 14..20)],
            None,
        ),
        ("use a with", false, Some(6), vec![(Missing, 10..10)], None),
        (
            "use a with @",
            false,
            Some(6),
            vec![(Whitespace, 10..11), (Error, 11..12)],
            None,
        ),
        (
            "use a with @ /*é*/ target",
            false,
            Some(6),
            vec![
                (Whitespace, 10..11),
                (Error, 11..12),
                (Whitespace, 12..13),
                (BlockComment, 13..19),
                (Whitespace, 19..20),
                (Identifier, 20..26),
            ],
            None,
        ),
        (
            "use a with target::",
            false,
            Some(6),
            vec![
                (Whitespace, 10..11),
                (Identifier, 11..17),
                (ColonColon, 17..19),
                (Missing, 19..19),
            ],
            None,
        ),
        (
            "use a with target/@",
            false,
            Some(6),
            vec![
                (Whitespace, 10..11),
                (Identifier, 11..17),
                (Slash, 17..18),
                (Error, 18..19),
            ],
            None,
        ),
        (
            "use a with target::@ next",
            false,
            Some(6),
            vec![
                (Whitespace, 10..11),
                (Identifier, 11..17),
                (ColonColon, 17..19),
                (Error, 19..20),
                (Whitespace, 20..21),
                (Identifier, 21..25),
            ],
            None,
        ),
        (
            "use a with ;next",
            false,
            Some(6),
            vec![(Missing, 10..10)],
            Some((10, 10..11, 11..12)),
        ),
        (
            "use a with target:: ;next",
            false,
            Some(6),
            vec![
                (Whitespace, 10..11),
                (Identifier, 11..17),
                (ColonColon, 17..19),
                (Missing, 19..19),
            ],
            Some((19, 19..20, 20..21)),
        ),
    ] {
        let operators = OperatorTable::empty();
        let mut input = source;
        let mut recover = Recover::new_for_test(&operators);
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(Root.into());
        let mut exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
        if let Err(Either::Right(end)) = &mut exit {
            emit_end(&mut builder, end);
        }
        builder.finish_node();
        let root = SyntaxNode::new_root(finish_with_discarded_recoveries(builder, recover));
        let end = pending.as_ref().map_or(source.len(), |(end, _, _)| *end) as u32;
        let tree = root
            .descendants()
            .find(|node| node.kind() == UseTree)
            .unwrap();
        assert_eq!(
            projection(&tree),
            [(UsePath, 4..5), (UseQualifiers, 5..end)],
            "{source:?}"
        );
        let initial = tree.children().next().unwrap();
        assert_eq!(projection(&initial), [(Identifier, 4..5)]);
        assert_eq!(
            initial
                .ancestors()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [UsePath, UseTree, UseDeclaration, Statement, Root]
        );
        let qualifiers = tree
            .children()
            .find(|node| node.kind() == UseQualifiers)
            .unwrap();
        assert_eq!(
            qualifiers
                .ancestors()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [UseQualifiers, UseTree, UseDeclaration, Statement, Root]
        );
        let mut expected = vec![(Whitespace, 5..6)];
        if version {
            expected.push((UseVersion, 6..8));
            if anchor_start.is_some() {
                expected.push((Whitespace, 8..9));
            }
        }
        if let Some(start) = anchor_start {
            expected.push((UseAnchor, start..end));
        }
        assert_eq!(projection(&qualifiers), expected);
        let versions: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == UseVersion)
            .collect();
        assert_eq!(versions.len(), usize::from(version));
        if let Some(node) = versions.first() {
            assert_eq!(node.parent().as_ref(), Some(&qualifiers));
            assert_eq!(projection(node), [(Version, 6..8)]);
        }
        let anchors: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == UseAnchor)
            .collect();
        assert_eq!(anchors.len(), usize::from(anchor_start.is_some()));
        let paths: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == UsePath)
            .collect();
        assert_eq!(paths.len(), 1 + anchors.len());
        if let Some(start) = anchor_start {
            let anchor = &anchors[0];
            assert_eq!(anchor.parent().as_ref(), Some(&qualifiers));
            assert_eq!(
                projection(anchor),
                [(WithKw, start..start + 4), (UsePath, start + 4..end)]
            );
            let path = &paths[1];
            assert_eq!(path.parent().as_ref(), Some(anchor));
            assert_eq!(
                path.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
                [
                    UsePath,
                    UseAnchor,
                    UseQualifiers,
                    UseTree,
                    UseDeclaration,
                    Statement,
                    Root
                ]
            );
            assert_eq!(projection(path), path_children);
            let mut runs = Vec::new();
            let mut current: Option<std::ops::Range<u32>> = None;
            for child in path.children_with_tokens() {
                assert_eq!(child.parent().as_ref(), Some(path));
                assert_eq!(child.as_node().is_some(), child.kind() == Missing);
                let range = child.text_range();
                if child.kind() == Error {
                    if let Some(run) = &mut current {
                        assert_eq!(run.end, u32::from(range.start()));
                        run.end = u32::from(range.end());
                    } else {
                        current = Some(u32::from(range.start())..u32::from(range.end()));
                    }
                } else if let Some(run) = current.take() {
                    runs.push(run);
                }
            }
            if let Some(run) = current {
                runs.push(run);
            }
            assert_eq!(
                runs,
                path_children
                    .iter()
                    .filter(|(kind, _)| *kind == Error)
                    .map(|(_, range)| range.clone())
                    .collect::<Vec<_>>()
            );
        }
        let recoveries: Vec<_> = root
            .descendants_with_tokens()
            .filter(|child| matches!(child.kind(), Missing | Error))
            .collect();
        let expected_recoveries: Vec<_> = path_children
            .iter()
            .filter(|(kind, _)| matches!(kind, Missing | Error))
            .collect();
        assert_eq!(recoveries.len(), expected_recoveries.len());
        for (child, (kind, range)) in recoveries.iter().zip(expected_recoveries) {
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.parent().as_ref(), paths.get(1));
            assert_eq!(
                child.text_range(),
                rowan::TextRange::new(range.start.into(), range.end.into())
            );
            if let Some(node) = child.as_node() {
                assert_eq!(*kind, Missing);
                assert!(node.text_range().is_empty());
                assert!(node.children_with_tokens().next().is_none());
            } else {
                assert_eq!(*kind, Error);
            }
        }
        for node in root.descendants() {
            for child in node.children_with_tokens() {
                assert_eq!(child.parent().as_ref(), Some(&node));
                assert_eq!(
                    child.as_node().is_some(),
                    matches!(
                        child.kind(),
                        Statement
                            | UseDeclaration
                            | UseTree
                            | UsePath
                            | UseQualifiers
                            | UseVersion
                            | UseAnchor
                            | Missing
                    )
                );
            }
        }
        for child in root.descendants_with_tokens() {
            let range = child.text_range();
            assert_eq!(
                child.to_string(),
                source[usize::from(range.start())..usize::from(range.end())]
            );
            assert!(!matches!(child.kind(), Invalid | UseGroupForeignClose));
        }
        if let Some((end, leading, payload)) = pending {
            assert_eq!(root.to_string(), source[..end]);
            let Err(Either::Left(mut item)) = exit else {
                panic!("protected semicolon must remain pending")
            };
            assert_eq!(token_kind(&item), Some(TokenKind::Semicolon));
            assert_eq!(item.payload_view().spelling(), Some(";"));
            let extent = item.extent(source.len() - input.len());
            assert_eq!(extent.leading(), leading.clone());
            assert_eq!(extent.payload(), payload);
            let leading_text = emit_pending_leading_text(&mut item);
            assert_eq!(leading_text, source[leading]);
            assert_eq!(input, "next");
            assert_eq!(format!("{root}{leading_text};{input}"), source);
        } else {
            assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
            assert_eq!(input, "");
            assert_eq!(root.to_string(), source);
        }
    }
}

#[test]
fn use_schema_glob_repeated_exclusion_episodes() {
    use SyntaxKind::*;

    let projection = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    u32::from(range.start())..u32::from(range.end()),
                )
            })
            .collect::<Vec<_>>()
    };
    for (suffix, tail, pending) in [
        (
            ", b",
            vec![
                (Comma, 18..19),
                (Whitespace, 19..20),
                (UseExclusion, 20..21),
            ],
            None,
        ),
        (
            ", b, c",
            vec![
                (Comma, 18..19),
                (Whitespace, 19..20),
                (UseExclusion, 20..21),
                (Comma, 21..22),
                (Whitespace, 22..23),
                (UseExclusion, 23..24),
            ],
            None,
        ),
        (",", vec![(Comma, 18..19), (Missing, 19..19)], None),
        (
            ", ;next",
            vec![(Comma, 18..19), (Missing, 19..19)],
            Some((19, 19..20, 20..21, ";", "next")),
        ),
        (
            ", @",
            vec![(Comma, 18..19), (Whitespace, 19..20), (Error, 20..21)],
            None,
        ),
        (
            ", @ /*é*/ b",
            vec![
                (Comma, 18..19),
                (Whitespace, 19..20),
                (Error, 20..21),
                (UseExclusion, 21..30),
            ],
            None,
        ),
        (
            ", @, b",
            vec![(Comma, 18..19), (Whitespace, 19..20), (Error, 20..21)],
            Some((21, 21..21, 21..22, ",", " b")),
        ),
        (
            ", (b,c)",
            vec![
                (Comma, 18..19),
                (Whitespace, 19..20),
                (UseExclusion, 20..25),
            ],
            None,
        ),
        (
            ", (+)",
            vec![
                (Comma, 18..19),
                (Whitespace, 19..20),
                (UseExclusion, 20..23),
            ],
            None,
        ),
        (" v1 with anchor", vec![], None),
    ] {
        let source = format!("use x::* without a{suffix}");
        let operators = OperatorTable::empty();
        let mut input = source.as_str();
        let mut recover = Recover::new_for_test(&operators);
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(Root.into());
        let mut exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
        if let Err(Either::Right(end)) = &mut exit {
            emit_end(&mut builder, end);
        }
        builder.finish_node();
        let root = SyntaxNode::new_root(finish_with_discarded_recoveries(builder, recover));
        let glob = root
            .descendants()
            .find(|node| node.kind() == UseGlob)
            .unwrap();
        assert_eq!(
            glob.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
            [UseGlob, UseTree, UseDeclaration, Statement, Root]
        );
        let mut expected = vec![
            (Star, 7..8),
            (Whitespace, 8..9),
            (WithoutKw, 9..16),
            (Whitespace, 16..17),
            (UseExclusion, 17..18),
        ];
        expected.extend(tail);
        assert_eq!(projection(&glob), expected, "{source:?}");
        let exclusions: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == UseExclusion)
            .collect();
        assert_eq!(
            exclusions.len(),
            expected
                .iter()
                .filter(|(kind, _)| *kind == UseExclusion)
                .count()
        );
        for exclusion in &exclusions {
            assert_eq!(exclusion.parent().as_ref(), Some(&glob));
            assert_eq!(
                exclusion
                    .ancestors()
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                [
                    UseExclusion,
                    UseGlob,
                    UseTree,
                    UseDeclaration,
                    Statement,
                    Root
                ]
            );
            let range = exclusion.text_range();
            let start = u32::from(range.start());
            let end = u32::from(range.end());
            let children = match (start, end) {
                (21, 30) => vec![
                    (Whitespace, 21..22),
                    (BlockComment, 22..28),
                    (Whitespace, 28..29),
                    (Identifier, 29..30),
                ],
                (20, 25) => vec![(UseExclusionGroup, 20..25)],
                (20, 23) => vec![(OperatorName, 20..23)],
                _ => vec![(Identifier, start..end)],
            };
            assert_eq!(projection(exclusion), children);
            for child in exclusion.children_with_tokens() {
                assert_eq!(child.parent().as_ref(), Some(exclusion));
                assert_eq!(
                    child.as_node().is_some(),
                    matches!(child.kind(), UseExclusionGroup | OperatorName)
                );
                if let Some(node) = child.as_node() {
                    let nested = if node.kind() == UseExclusionGroup {
                        vec![
                            (LParen, 20..21),
                            (UseTree, 21..22),
                            (Comma, 22..23),
                            (UseTree, 23..24),
                            (RParen, 24..25),
                        ]
                    } else {
                        vec![(LParen, 20..21), (Operator, 21..22), (RParen, 22..23)]
                    };
                    assert_eq!(projection(node), nested);
                    for nested in node.children_with_tokens() {
                        assert_eq!(nested.parent().as_ref(), Some(node));
                        assert_eq!(nested.as_node().is_some(), nested.kind() == UseTree);
                    }
                }
            }
        }
        let mut runs = Vec::new();
        let mut current: Option<std::ops::Range<u32>> = None;
        for child in glob.children_with_tokens() {
            assert_eq!(child.parent().as_ref(), Some(&glob));
            assert_eq!(
                child.as_node().is_some(),
                matches!(child.kind(), Missing | UseExclusion)
            );
            let range = child.text_range();
            // A run is selected by direct adjacency, never malformed spelling.
            if child.kind() == Error {
                if let Some(run) = &mut current {
                    assert_eq!(run.end, u32::from(range.start()));
                    run.end = u32::from(range.end());
                } else {
                    current = Some(u32::from(range.start())..u32::from(range.end()));
                }
            } else if let Some(run) = current.take() {
                runs.push(run);
            }
        }
        if let Some(run) = current {
            runs.push(run);
        }
        let expected_errors: Vec<_> = expected
            .iter()
            .filter(|(kind, _)| *kind == Error)
            .map(|(_, range)| range.clone())
            .collect();
        assert_eq!(runs, expected_errors);
        let errors: Vec<_> = root
            .descendants_with_tokens()
            .filter(|child| child.kind() == Error)
            .collect();
        assert_eq!(errors.len(), expected_errors.len());
        assert!(
            errors
                .iter()
                .all(|child| child.as_token().is_some() && child.parent().as_ref() == Some(&glob))
        );
        let missing: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect();
        assert_eq!(
            missing.len(),
            expected.iter().filter(|(kind, _)| *kind == Missing).count()
        );
        for node in missing {
            assert_eq!(node.parent().as_ref(), Some(&glob));
            assert_eq!(node.text_range(), rowan::TextRange::empty(19.into()));
            assert!(node.children_with_tokens().next().is_none());
        }
        let qualifiers: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == UseQualifiers)
            .collect();
        assert_eq!(qualifiers.len(), usize::from(suffix == " v1 with anchor"));
        if let Some(qualifiers) = qualifiers.first() {
            let tree = glob.parent().unwrap();
            assert_eq!(qualifiers.parent().as_ref(), Some(&tree));
            assert_eq!(
                projection(&tree),
                [
                    (UsePath, 4..5),
                    (ColonColon, 5..7),
                    (UseGlob, 7..18),
                    (UseQualifiers, 18..33)
                ]
            );
            assert_eq!(
                projection(qualifiers),
                [
                    (Whitespace, 18..19),
                    (UseVersion, 19..21),
                    (Whitespace, 21..22),
                    (UseAnchor, 22..33)
                ]
            );
            let version = qualifiers
                .children()
                .find(|node| node.kind() == UseVersion)
                .unwrap();
            assert_eq!(projection(&version), [(Version, 19..21)]);
            let anchor = qualifiers
                .children()
                .find(|node| node.kind() == UseAnchor)
                .unwrap();
            assert_eq!(projection(&anchor), [(WithKw, 22..26), (UsePath, 26..33)]);
            let path = anchor.children().next().unwrap();
            assert_eq!(
                projection(&path),
                [(Whitespace, 26..27), (Identifier, 27..33)]
            );
            for node in [qualifiers, &version, &anchor, &path] {
                for child in node.children_with_tokens() {
                    assert_eq!(child.parent().as_ref(), Some(node));
                    assert_eq!(
                        child.as_node().is_some(),
                        matches!(child.kind(), UseVersion | UseAnchor | UsePath)
                    );
                }
            }
        }
        for child in root.descendants_with_tokens() {
            let range = child.text_range();
            assert_eq!(
                child.to_string(),
                source[usize::from(range.start())..usize::from(range.end())]
            );
            assert!(!matches!(child.kind(), Invalid | UseGroupForeignClose));
        }
        if let Some((end, leading, payload, spelling, remainder)) = pending {
            assert_eq!(root.to_string(), source[..end]);
            let Err(Either::Left(mut item)) = exit else {
                panic!("boundary Item must remain pending")
            };
            let extent = item.extent(source.len() - input.len());
            assert_eq!(extent.leading(), leading.clone());
            assert_eq!(extent.payload(), payload);
            assert_eq!(item.payload_view().spelling(), Some(spelling));
            assert_eq!(input, remainder);
            let leading_text = emit_pending_leading_text(&mut item);
            assert_eq!(leading_text, source[leading]);
            assert_eq!(format!("{root}{leading_text}{spelling}{input}"), source);
        } else {
            assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
            assert_eq!(input, "");
            assert_eq!(root.to_string(), source);
        }
    }
}

#[test]
fn use_schema_glob_unseparated_exclusion_not_admitted() {
    use SyntaxKind::*;

    let projection = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    u32::from(range.start())..u32::from(range.end()),
                )
            })
            .collect::<Vec<_>>()
    };
    for gap in [" ", "\n", "\r\n"] {
        for comma in [false, true] {
            let separator = if comma { "," } else { "" };
            let source = format!("use p::* without a{separator}{gap}b");
            let mut fresh: Option<(
                GreenNode,
                Vec<crate::recovery_record::CommittedRecoveryRecord>,
            )> = None;
            for frozen in [false, true] {
                let operators = OperatorTable::empty();
                let mut input = source.as_str();
                let mut recover = if frozen {
                    Recover::reconcile_for_test(&operators, &fresh.as_ref().unwrap().1)
                } else {
                    Recover::new_for_test(&operators)
                };
                let mut builder = GreenNodeBuilder::new();
                builder.start_node(Root.into());
                let exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
                builder.finish_node();
                let green = builder.finish();
                let records = recover.finish_recoveries_for_test();
                assert!(records.is_empty(), "{source:?}");
                if let Some((fresh_green, fresh_records)) = &fresh {
                    assert_eq!(&green, fresh_green);
                    assert_eq!(&records, fresh_records);
                } else {
                    fresh = Some((green.clone(), records));
                }
                let root = SyntaxNode::new_root(green);
                let glob = root
                    .descendants()
                    .find(|node| node.kind() == UseGlob)
                    .unwrap();
                assert_eq!(
                    glob.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
                    [UseGlob, UseTree, UseDeclaration, Statement, Root]
                );
                let mut expected = vec![
                    (Star, 7..8),
                    (Whitespace, 8..9),
                    (WithoutKw, 9..16),
                    (Whitespace, 16..17),
                    (UseExclusion, 17..18),
                ];
                let payload_start = 18 + usize::from(comma) + gap.len();
                let glob_end = if comma { source.len() } else { 18 };
                if comma {
                    expected.extend([
                        (Comma, 18..19),
                        (
                            if gap == " " { Whitespace } else { Newline },
                            19..payload_start as u32,
                        ),
                        (UseExclusion, payload_start as u32..source.len() as u32),
                    ]);
                }
                assert_eq!(projection(&glob), expected, "{source:?}");
                assert_eq!(
                    glob.text_range(),
                    rowan::TextRange::new(7.into(), (glob_end as u32).into())
                );
                for child in glob.children_with_tokens() {
                    assert_eq!(child.parent().as_ref(), Some(&glob));
                    assert_eq!(child.as_node().is_some(), child.kind() == UseExclusion);
                }
                let exclusions: Vec<_> = root
                    .descendants()
                    .filter(|node| node.kind() == UseExclusion)
                    .collect();
                assert_eq!(exclusions.len(), 1 + usize::from(comma));
                for (index, exclusion) in exclusions.iter().enumerate() {
                    let start = if index == 0 { 17 } else { payload_start as u32 };
                    assert_eq!(exclusion.parent().as_ref(), Some(&glob));
                    assert_eq!(projection(exclusion), [(Identifier, start..start + 1)]);
                    assert!(exclusion.children_with_tokens().all(|child| {
                        child.as_token().is_some() && child.parent().as_ref() == Some(exclusion)
                    }));
                }
                for child in root.descendants_with_tokens() {
                    assert!(!matches!(child.kind(), Missing | Error | Invalid));
                    if !comma {
                        assert_ne!(child.kind(), Comma);
                    }
                    let range = child.text_range();
                    assert_eq!(
                        child.to_string(),
                        source[usize::from(range.start())..usize::from(range.end())]
                    );
                }
                assert_eq!(input, "");
                assert_eq!(root.to_string(), source[..glob_end]);
                if comma {
                    assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
                } else {
                    // No outer comma means no repeated exclusion episode was admitted.
                    let Err(Either::Left(mut pending)) = exit else {
                        panic!("unseparated identifier must remain pending")
                    };
                    let origin = source.len() - input.len();
                    assert_eq!(origin, payload_start + 1);
                    let extent = pending.extent(origin);
                    assert_eq!(extent.leading(), 18..payload_start);
                    assert_eq!(extent.payload(), payload_start..payload_start + 1);
                    assert_eq!(pending.payload_view().spelling(), Some("b"));
                    let leading = emit_pending_leading_text(&mut pending);
                    assert_eq!(leading, gap);
                    assert_eq!(format!("{root}{leading}b{input}"), source);
                }
            }
        }
    }
}

#[test]
fn use_schema_glob_pre_comma_trivia_keeps_comma_pending() {
    use SyntaxKind::*;

    let projection = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    u32::from(range.start())..u32::from(range.end()),
                )
            })
            .collect::<Vec<_>>()
    };
    for (gap, trivia) in [
        (" ", vec![(Whitespace, 0..1)]),
        ("\n", vec![(Newline, 0..1)]),
        ("\r\n", vec![(Newline, 0..2)]),
        ("/*é*/", vec![(BlockComment, 0..6)]),
        (
            " /* comment\n */ ",
            vec![
                (Whitespace, 0..1),
                (BlockComment, 1..15),
                (Whitespace, 15..16),
            ],
        ),
    ] {
        for immediate_comma in [false, true] {
            let source = if immediate_comma {
                format!("use p::* without a,{gap}b")
            } else {
                format!("use p::* without a{gap},b")
            };
            let mut fresh: Option<(GreenNode, Vec<CommittedRecoveryRecord>)> = None;
            for frozen in [false, true] {
                let operators = OperatorTable::empty();
                let mut input = source.as_str();
                let mut recover = if frozen {
                    Recover::reconcile_for_test(&operators, &fresh.as_ref().unwrap().1)
                } else {
                    Recover::new_for_test(&operators)
                };
                let mut builder = GreenNodeBuilder::new();
                builder.start_node(Root.into());
                let exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
                builder.finish_node();
                let green = builder.finish();
                let records = recover.finish_recoveries_for_test();
                assert!(records.is_empty(), "{source:?}");
                if let Some((fresh_green, fresh_records)) = &fresh {
                    assert_eq!(&green, fresh_green, "{source:?}");
                    assert_eq!(&records, fresh_records, "{source:?}");
                } else {
                    fresh = Some((green.clone(), records));
                }
                let root = SyntaxNode::new_root(green);
                let glob = root
                    .descendants()
                    .find(|node| node.kind() == UseGlob)
                    .unwrap();
                assert_eq!(
                    glob.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
                    [UseGlob, UseTree, UseDeclaration, Statement, Root]
                );
                let mut expected = vec![
                    (Star, 7..8),
                    (Whitespace, 8..9),
                    (WithoutKw, 9..16),
                    (Whitespace, 16..17),
                    (UseExclusion, 17..18),
                ];
                if immediate_comma {
                    expected.push((Comma, 18..19));
                    expected.extend(
                        trivia
                            .iter()
                            .map(|(kind, range)| (*kind, 19 + range.start..19 + range.end)),
                    );
                    expected.push((UseExclusion, 19 + gap.len() as u32..source.len() as u32));
                }
                assert_eq!(projection(&glob), expected, "{source:?}");
                let glob_end = if immediate_comma { source.len() } else { 18 };
                assert_eq!(
                    glob.text_range(),
                    rowan::TextRange::new(7.into(), (glob_end as u32).into())
                );
                for child in glob.children_with_tokens() {
                    assert_eq!(child.parent().as_ref(), Some(&glob));
                    assert_eq!(child.as_node().is_some(), child.kind() == UseExclusion);
                }
                let exclusions: Vec<_> = root
                    .descendants()
                    .filter(|node| node.kind() == UseExclusion)
                    .collect();
                assert_eq!(exclusions.len(), 1 + usize::from(immediate_comma));
                for (index, exclusion) in exclusions.iter().enumerate() {
                    let start = if index == 0 {
                        17
                    } else {
                        19 + gap.len() as u32
                    };
                    assert_eq!(exclusion.parent().as_ref(), Some(&glob));
                    assert_eq!(projection(exclusion), [(Identifier, start..start + 1)]);
                    assert!(
                        exclusion
                            .children_with_tokens()
                            .all(|child| child.as_token().is_some()
                                && child.parent().as_ref() == Some(exclusion))
                    );
                }
                for child in root.descendants_with_tokens() {
                    assert!(!matches!(child.kind(), Missing | Error | Invalid));
                    if !immediate_comma {
                        assert_ne!(child.kind(), Comma);
                    }
                    let range = child.text_range();
                    assert_eq!(
                        child.to_string(),
                        source[usize::from(range.start())..usize::from(range.end())]
                    );
                }
                assert_eq!(root.to_string(), source[..glob_end]);
                if immediate_comma {
                    assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
                    assert_eq!(input, "");
                } else {
                    let Err(Either::Left(mut pending)) = exit else {
                        panic!("comma with leading trivia must remain pending: {source:?}")
                    };
                    assert_eq!(input, "b");
                    let payload_start = 18 + gap.len();
                    let extent = pending.extent(source.len() - input.len());
                    assert_eq!(extent.leading(), 18..payload_start);
                    assert_eq!(extent.payload(), payload_start..payload_start + 1);
                    assert_eq!(pending.payload_view().spelling(), Some(","));
                    let leading = emit_pending_leading_text(&mut pending);
                    assert_eq!(leading, gap);
                    assert_eq!(format!("{root}{leading},{input}"), source);
                }
            }
        }
    }
}

#[test]
fn use_schema_glob_post_comma_boundary_missing_handoff() {
    use crate::recovery_record::*;
    use SyntaxKind::*;

    for (gap, spelling, stops) in [
        ("", "", 0),
        ("\n", ";", 0),
        ("\r\n  ", ")", 0),
        (" /* comment\n */ ", "]", 0),
        ("\n", "}", 0),
        ("\r\n  ", "->", STOP_ARROW),
    ] {
        let remainder = if spelling.is_empty() { "" } else { "next" };
        let source = format!("use p::* without a,{gap}{spelling}{remainder}");
        let mut fresh: Option<(
            GreenNode,
            Vec<crate::recovery_record::CommittedRecoveryRecord>,
        )> = None;
        for frozen in [false, true] {
            let operators = OperatorTable::empty();
            let mut input = source.as_str();
            let mut recover = if frozen {
                let (_, records) = fresh.as_ref().unwrap();
                Recover::reconcile_for_test(&operators, records)
            } else {
                Recover::new_for_test(&operators)
            };
            let mut builder = GreenNodeBuilder::new();
            builder.start_node(Root.into());
            let exit = statement(
                SyntaxIn::new(&mut input, &mut recover, &mut builder),
                0,
                stops,
            );
            builder.finish_node();
            let green = builder.finish();
            let records = recover.finish_recoveries_for_test();
            if spelling == ";" {
                let role = GrammarRole::Declaration(DeclarationRole::Import(ImportRole::Path));
                assert_eq!(
                    records,
                    [CommittedRecoveryRecord {
                        id: DiagnosticId(0),
                        site: RecoverySiteKey {
                            role,
                            range: 19..19,
                        },
                        kind: RecoveryKind::Missing,
                        unexpected: std::sync::Arc::from([]),
                        expectations: std::sync::Arc::from([SyntaxExpectation {
                            role,
                            expected: ExpectedSyntax::Path,
                            range: 19..19,
                            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                        }]),
                        primary_expectation: 0,
                    }]
                );
            }
            if let Some((fresh_green, fresh_records)) = &fresh {
                assert_eq!(&green, fresh_green);
                assert_eq!(&records, fresh_records);
            } else {
                fresh = Some((green.clone(), records));
            }
            let root = SyntaxNode::new_root(green);
            let glob = root
                .descendants()
                .find(|node| node.kind() == UseGlob)
                .unwrap();
            assert_eq!(
                glob.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
                [UseGlob, UseTree, UseDeclaration, Statement, Root]
            );
            assert_eq!(
                glob.children_with_tokens()
                    .map(|child| {
                        assert_eq!(child.parent().as_ref(), Some(&glob));
                        assert_eq!(
                            child.as_node().is_some(),
                            matches!(child.kind(), UseExclusion | Missing)
                        );
                        let range = child.text_range();
                        (
                            child.kind(),
                            u32::from(range.start())..u32::from(range.end()),
                        )
                    })
                    .collect::<Vec<_>>(),
                [
                    (Star, 7..8),
                    (Whitespace, 8..9),
                    (WithoutKw, 9..16),
                    (Whitespace, 16..17),
                    (UseExclusion, 17..18),
                    (Comma, 18..19),
                    (Missing, 19..19)
                ]
            );
            let missing: Vec<_> = root
                .descendants()
                .filter(|node| node.kind() == Missing)
                .collect();
            assert_eq!(missing.len(), 1);
            assert_eq!(missing[0].parent().as_ref(), Some(&glob));
            assert!(missing[0].children_with_tokens().next().is_none());
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == UseExclusion)
                    .count(),
                1
            );
            for child in root.descendants_with_tokens() {
                assert!(!matches!(child.kind(), Error | Invalid));
                let range = child.text_range();
                assert_eq!(
                    child.to_string(),
                    source[usize::from(range.start())..usize::from(range.end())]
                );
            }
            assert_eq!(root.to_string(), source[..19]);
            assert_eq!(input, remainder);
            if spelling.is_empty() {
                assert!(matches!(exit, Err(Either::Right(_))));
            } else {
                let Err(Either::Left(mut pending)) = exit else {
                    panic!("post-comma boundary must remain pending")
                };
                let payload_start = 19 + gap.len();
                let extent = pending.extent(source.len() - input.len());
                assert_eq!(extent.leading(), 19..payload_start);
                assert_eq!(
                    extent.payload(),
                    payload_start..payload_start + spelling.len()
                );
                assert_eq!(pending.payload_view().spelling(), Some(spelling));
                let leading = emit_pending_leading_text(&mut pending);
                assert_eq!(leading, gap);
                assert_eq!(format!("{root}{leading}{spelling}{input}"), source);
            }
        }
    }
}

#[test]
fn use_schema_glob_post_comma_reserved_with_handoff() {
    use crate::recovery_record::*;
    use SyntaxKind::*;

    let source = "use p::* without a, with";
    let role = GrammarRole::Declaration(DeclarationRole::Import(ImportRole::Path));
    let expected_records = vec![CommittedRecoveryRecord {
        id: DiagnosticId(0),
        site: RecoverySiteKey {
            role,
            range: 20..20,
        },
        kind: RecoveryKind::Missing,
        unexpected: std::sync::Arc::from([]),
        expectations: std::sync::Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Path,
            range: 20..20,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }];
    let mut fresh = None;
    for frozen in [false, true] {
        let operators = OperatorTable::empty();
        let mut input = source;
        let mut recover = if frozen {
            Recover::reconcile_for_test(&operators, &expected_records)
        } else {
            Recover::new_for_test(&operators)
        };
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(Root.into());
        let exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
        builder.finish_node();
        let green = builder.finish();
        let records = recover.finish_recoveries_for_test();
        assert_eq!(records, expected_records);
        if let Some((fresh_green, fresh_records)) = &fresh {
            assert_eq!(&green, fresh_green);
            assert_eq!(&records, fresh_records);
        } else {
            fresh = Some((green.clone(), records));
        }
        let root = SyntaxNode::new_root(green);
        let glob = root
            .descendants()
            .find(|node| node.kind() == UseGlob)
            .unwrap();
        assert_eq!(
            glob.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
            [UseGlob, UseTree, UseDeclaration, Statement, Root]
        );
        assert_eq!(
            glob.children_with_tokens()
                .map(|child| {
                    let range = child.text_range();
                    assert_eq!(child.parent().as_ref(), Some(&glob));
                    assert_eq!(
                        child.as_node().is_some(),
                        matches!(child.kind(), UseExclusion | Missing)
                    );
                    (
                        child.kind(),
                        u32::from(range.start())..u32::from(range.end()),
                    )
                })
                .collect::<Vec<_>>(),
            [
                (Star, 7..8),
                (Whitespace, 8..9),
                (WithoutKw, 9..16),
                (Whitespace, 16..17),
                (UseExclusion, 17..18),
                (Comma, 18..19),
                (Whitespace, 19..20),
                (Missing, 20..20),
            ]
        );
        let exclusions: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == UseExclusion)
            .collect();
        assert_eq!(exclusions.len(), 1);
        let payloads: Vec<_> = exclusions[0].children_with_tokens().collect();
        assert_eq!(payloads.len(), 1);
        assert!(payloads[0].as_token().is_some());
        assert_eq!(payloads[0].kind(), Identifier);
        assert_eq!(
            payloads[0].text_range(),
            rowan::TextRange::new(17.into(), 18.into())
        );
        let missing: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect();
        assert_eq!(missing.len(), 1);
        assert_eq!(missing[0].parent().as_ref(), Some(&glob));
        assert_eq!(missing[0].text_range(), rowan::TextRange::empty(20.into()));
        assert!(missing[0].children_with_tokens().next().is_none());
        for child in root.descendants_with_tokens() {
            assert!(!matches!(
                child.kind(),
                Error | Invalid | UseQualifiers | UseAnchor
            ));
            let range = child.text_range();
            assert_eq!(
                child.to_string(),
                source[usize::from(range.start())..usize::from(range.end())]
            );
        }
        assert_eq!(root.to_string(), source[..20]);
        let Err(Either::Left(mut pending)) = exit else {
            panic!("reserved with must remain pending")
        };
        let extent = pending.extent(source.len() - input.len());
        assert_eq!(extent.leading(), 19..20);
        assert_eq!(extent.payload(), 20..24);
        assert_eq!(pending.payload_view().spelling(), Some("with"));
        assert_eq!(input, "");
        // The comma phase already emitted the original leading under Glob.
        let remaining_leading = emit_pending_leading_text(&mut pending);
        assert_eq!(remaining_leading, "");
        assert_eq!(format!("{root}{remaining_leading}with{input}"), source);
    }
}

#[test]
fn use_schema_glob_first_required_exclusion_inline_gap() {
    use crate::recovery_record::*;
    use SyntaxKind::*;

    let projection = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|child| {
                assert_eq!(child.parent().as_ref(), Some(node));
                let range = child.text_range();
                (
                    child.kind(),
                    u32::from(range.start())..u32::from(range.end()),
                )
            })
            .collect::<Vec<_>>()
    };
    for (payload, delimiters) in [
        ("(a)", Some((LParen, RParen))),
        ("{a}", Some((LBrace, RBrace))),
        ("*", None),
    ] {
        for gap in ["", " "] {
            let source = format!("use p::* without{gap}{payload}");
            let start = 16 + gap.len() as u32;
            let end = start + payload.len() as u32;
            let mut fresh: Option<(GreenNode, Vec<CommittedRecoveryRecord>)> = None;
            for frozen in [false, true] {
                let operators = OperatorTable::empty();
                let mut input = source.as_str();
                let mut recover = if frozen {
                    Recover::reconcile_for_test(&operators, &fresh.as_ref().unwrap().1)
                } else {
                    Recover::new_for_test(&operators)
                };
                let mut builder = GreenNodeBuilder::new();
                builder.start_node(Root.into());
                let mut exit =
                    statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
                if let Err(Either::Right(end)) = &mut exit {
                    emit_end(&mut builder, end);
                }
                assert!(matches!(exit, Err(Either::Right(_))));
                builder.finish_node();
                let green = builder.finish();
                let records = recover.finish_recoveries_for_test();
                // Records check migration parity; CST ownership is asserted below.
                if gap.is_empty() && payload == "(a)" {
                    let role = GrammarRole::Declaration(DeclarationRole::Import(ImportRole::Path));
                    assert_eq!(
                        records,
                        [CommittedRecoveryRecord {
                            id: DiagnosticId(0),
                            site: RecoverySiteKey {
                                role,
                                range: 16..16
                            },
                            kind: RecoveryKind::Missing,
                            unexpected: std::sync::Arc::from([]),
                            expectations: std::sync::Arc::from([SyntaxExpectation {
                                role,
                                expected: ExpectedSyntax::Path,
                                range: 16..16,
                                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                            }]),
                            primary_expectation: 0,
                        }]
                    );
                }
                if !gap.is_empty() {
                    assert!(records.is_empty());
                }
                if let Some((fresh_green, fresh_records)) = &fresh {
                    assert_eq!(&green, fresh_green);
                    assert_eq!(&records, fresh_records);
                } else {
                    fresh = Some((green.clone(), records));
                }
                let root = SyntaxNode::new_root(green);
                let glob = root
                    .descendants()
                    .find(|node| node.kind() == UseGlob)
                    .unwrap();
                assert_eq!(
                    glob.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
                    [UseGlob, UseTree, UseDeclaration, Statement, Root]
                );
                assert_eq!(
                    projection(&glob),
                    [
                        (Star, 7..8),
                        (Whitespace, 8..9),
                        (WithoutKw, 9..16),
                        if gap.is_empty() {
                            (Missing, 16..16)
                        } else {
                            (Whitespace, 16..17)
                        },
                        (UseExclusion, start..end),
                    ],
                    "{source:?}"
                );
                assert!(
                    glob.children_with_tokens()
                        .all(|child| child.as_node().is_some()
                            == matches!(child.kind(), Missing | UseExclusion))
                );
                let missing: Vec<_> = root
                    .descendants()
                    .filter(|node| node.kind() == Missing)
                    .collect();
                assert_eq!(missing.len(), usize::from(gap.is_empty()));
                for node in missing {
                    assert_eq!(node.parent().as_ref(), Some(&glob));
                    assert!(node.children_with_tokens().next().is_none());
                }
                let exclusions: Vec<_> = root
                    .descendants()
                    .filter(|node| node.kind() == UseExclusion)
                    .collect();
                assert_eq!(exclusions.len(), 1);
                let exclusion = &exclusions[0];
                assert_eq!(exclusion.parent().as_ref(), Some(&glob));
                if let Some((open, close)) = delimiters {
                    assert_eq!(projection(exclusion), [(UseExclusionGroup, start..end)]);
                    let group = exclusion.children().next().unwrap();
                    assert_eq!(
                        projection(&group),
                        [
                            (open, start..start + 1),
                            (UseTree, start + 1..end - 1),
                            (close, end - 1..end)
                        ]
                    );
                    assert!(
                        group
                            .children_with_tokens()
                            .all(|child| child.as_node().is_some() == (child.kind() == UseTree))
                    );
                    let tree = group.children().next().unwrap();
                    assert_eq!(projection(&tree), [(UsePath, start + 1..end - 1)]);
                    let path = tree.children().next().unwrap();
                    assert_eq!(projection(&path), [(Identifier, start + 1..end - 1)]);
                    assert!(
                        path.children_with_tokens()
                            .all(|child| child.as_token().is_some())
                    );
                } else {
                    assert_eq!(projection(exclusion), [(Star, start..end)]);
                    assert!(
                        exclusion
                            .children_with_tokens()
                            .all(|child| child.as_token().is_some())
                    );
                }
                for child in root.descendants_with_tokens() {
                    assert!(!matches!(child.kind(), Error | Invalid));
                    let range = child.text_range();
                    assert_eq!(
                        child.to_string(),
                        source[usize::from(range.start())..usize::from(range.end())]
                    );
                }
                assert_eq!(
                    root.text_range(),
                    rowan::TextRange::new(0.into(), end.into())
                );
                assert_eq!(root.to_string(), source);
                assert_eq!(input, "");
            }
        }
    }
}

#[test]
fn use_schema_glob_first_required_exclusion_admission() {
    use SyntaxKind::*;

    let projection = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    u32::from(range.start())..u32::from(range.end()),
                )
            })
            .collect::<Vec<_>>()
    };
    for (suffix, tail, exclusion_children, pending) in [
        (
            " z",
            vec![(Whitespace, 16..17), (UseExclusion, 17..18)],
            vec![(Identifier, 17..18)],
            None,
        ),
        ("", vec![(Missing, 16..16)], vec![], None),
        (
            " ;next",
            vec![(Missing, 16..16)],
            vec![],
            Some((16, 16..17, 17..18, ";", "next")),
        ),
        (
            " with anchor",
            vec![(Whitespace, 16..17), (Missing, 17..17)],
            vec![],
            Some((17, 16..17, 17..21, "with", " anchor")),
        ),
        (
            " @",
            vec![(Whitespace, 16..17), (Error, 17..18)],
            vec![],
            None,
        ),
        (
            " @ /*é*/ z",
            vec![
                (Whitespace, 16..17),
                (Error, 17..18),
                (UseExclusion, 18..27),
            ],
            vec![
                (Whitespace, 18..19),
                (BlockComment, 19..25),
                (Whitespace, 25..26),
                (Identifier, 26..27),
            ],
            None,
        ),
        (
            " @, z",
            vec![(Whitespace, 16..17), (Error, 17..18)],
            vec![],
            Some((18, 18..18, 18..19, ",", " z")),
        ),
        (
            " @(+)",
            vec![
                (Whitespace, 16..17),
                (Error, 17..18),
                (UseExclusion, 18..21),
            ],
            vec![(OperatorName, 18..21)],
            None,
        ),
    ] {
        let source = format!("use x::* without{suffix}");
        let operators = OperatorTable::empty();
        let mut input = source.as_str();
        let mut recover = Recover::new_for_test(&operators);
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(Root.into());
        let mut exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
        if let Err(Either::Right(end)) = &mut exit {
            emit_end(&mut builder, end);
        }
        builder.finish_node();
        let root = SyntaxNode::new_root(finish_with_discarded_recoveries(builder, recover));
        let glob = root
            .descendants()
            .find(|node| node.kind() == UseGlob)
            .unwrap();
        assert_eq!(
            glob.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
            [UseGlob, UseTree, UseDeclaration, Statement, Root]
        );
        let mut expected = vec![(Star, 7..8), (Whitespace, 8..9), (WithoutKw, 9..16)];
        expected.extend(tail);
        assert_eq!(projection(&glob), expected, "{source:?}");
        let mut runs = Vec::new();
        let mut current: Option<std::ops::Range<u32>> = None;
        for child in glob.children_with_tokens() {
            assert_eq!(child.parent().as_ref(), Some(&glob));
            assert_eq!(
                child.as_node().is_some(),
                matches!(child.kind(), Missing | UseExclusion)
            );
            let range = child.text_range();
            // Only immediate ownership and adjacency identify a raw occurrence.
            if child.kind() == Error {
                if let Some(run) = &mut current {
                    assert_eq!(run.end, u32::from(range.start()));
                    run.end = u32::from(range.end());
                } else {
                    current = Some(u32::from(range.start())..u32::from(range.end()));
                }
            } else if let Some(run) = current.take() {
                runs.push(run);
            }
        }
        if let Some(run) = current {
            runs.push(run);
        }
        let expected_errors: Vec<_> = expected
            .iter()
            .filter(|(kind, _)| *kind == Error)
            .map(|(_, range)| range.clone())
            .collect();
        assert_eq!(runs, expected_errors, "{source:?}");
        let exclusions: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == UseExclusion)
            .collect();
        assert_eq!(
            exclusions.len(),
            usize::from(!exclusion_children.is_empty()),
            "{source:?}"
        );
        if let Some(exclusion) = exclusions.first() {
            assert_eq!(exclusion.parent().as_ref(), Some(&glob));
            assert_eq!(
                exclusion
                    .ancestors()
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                [
                    UseExclusion,
                    UseGlob,
                    UseTree,
                    UseDeclaration,
                    Statement,
                    Root
                ]
            );
            assert_eq!(projection(exclusion), exclusion_children);
            // Raw retry may bring native leading into the dispatched exclusion.
            for child in exclusion.children_with_tokens() {
                assert_eq!(child.parent().as_ref(), Some(exclusion));
                assert_eq!(child.as_node().is_some(), child.kind() == OperatorName);
                if let Some(name) = child.as_node() {
                    assert_eq!(
                        projection(name),
                        [(LParen, 18..19), (Operator, 19..20), (RParen, 20..21)]
                    );
                    assert!(
                        name.children_with_tokens()
                            .all(|token| token.as_token().is_some()
                                && token.parent().as_ref() == Some(name))
                    );
                }
            }
        }
        let missing: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect();
        let expected_missing: Vec<_> = expected
            .iter()
            .filter(|(kind, _)| *kind == Missing)
            .map(|(_, range)| range.clone())
            .collect();
        assert_eq!(missing.len(), expected_missing.len());
        for (node, range) in missing.iter().zip(expected_missing) {
            assert_eq!(node.parent().as_ref(), Some(&glob));
            assert_eq!(
                node.text_range(),
                rowan::TextRange::new(range.start.into(), range.end.into())
            );
            assert!(node.text_range().is_empty());
            assert!(node.children_with_tokens().next().is_none());
        }
        let errors: Vec<_> = root
            .descendants_with_tokens()
            .filter(|child| child.kind() == Error)
            .collect();
        assert_eq!(errors.len(), expected_errors.len());
        assert!(
            errors
                .iter()
                .all(|child| child.as_token().is_some() && child.parent().as_ref() == Some(&glob))
        );
        for child in root.descendants_with_tokens() {
            let range = child.text_range();
            assert_eq!(
                child.to_string(),
                source[usize::from(range.start())..usize::from(range.end())]
            );
            assert!(!matches!(child.kind(), Invalid | UseGroupForeignClose));
        }
        if let Some((end, leading, payload, spelling, remainder)) = pending {
            assert_eq!(root.to_string(), source[..end]);
            let Err(Either::Left(mut item)) = exit else {
                panic!("boundary Item must remain pending")
            };
            let extent = item.extent(source.len() - input.len());
            assert_eq!(extent.leading(), leading.clone());
            assert_eq!(extent.payload(), payload.clone());
            assert_eq!(item.payload_view().spelling(), Some(spelling));
            assert_eq!(input, remainder);
            let leading_text = emit_pending_leading_text(&mut item);
            // Extent retains original leading even when the glob emitted it;
            // only source beyond the CST frontier remains pending.
            assert_eq!(leading_text, source[end..payload.start]);
            assert_eq!(format!("{root}{leading_text}{spelling}{input}"), source);
        } else {
            assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
            assert_eq!(input, "");
            assert_eq!(root.to_string(), source);
        }
    }
}

#[test]
fn use_schema_exclusion_form_dispatch() {
    use SyntaxKind::*;

    let projection = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|child| {
                let range = child.text_range();
                (
                    child.kind(),
                    u32::from(range.start())..u32::from(range.end()),
                )
            })
            .collect::<Vec<_>>()
    };
    for (text, payload_kind, children, recovery) in [
        ("name", Identifier, vec![], None),
        ("*", Star, vec![], None),
        (
            "{name}",
            UseExclusionGroup,
            vec![(LBrace, 17..18), (UseTree, 18..22), (RBrace, 22..23)],
            None,
        ),
        (
            "(name)",
            UseExclusionGroup,
            vec![(LParen, 17..18), (UseTree, 18..22), (RParen, 22..23)],
            None,
        ),
        (
            "()",
            UseExclusionGroup,
            vec![(LParen, 17..18), (RParen, 18..19)],
            None,
        ),
        (
            "(+)",
            OperatorName,
            vec![(LParen, 17..18), (Operator, 18..19), (RParen, 19..20)],
            None,
        ),
        (
            "( +)",
            UseExclusionGroup,
            vec![
                (LParen, 17..18),
                (Whitespace, 18..19),
                (Error, 19..20),
                (RParen, 20..21),
            ],
            Some((Error, 19..20)),
        ),
        (
            "{y::* without z}",
            UseExclusionGroup,
            vec![(LBrace, 17..18), (UseTree, 18..32), (RBrace, 32..33)],
            None,
        ),
        (
            "{name",
            UseExclusionGroup,
            vec![(LBrace, 17..18), (UseTree, 18..22), (Missing, 22..22)],
            Some((Missing, 22..22)),
        ),
        (
            "(name",
            UseExclusionGroup,
            vec![(LParen, 17..18), (UseTree, 18..22), (Missing, 22..22)],
            Some((Missing, 22..22)),
        ),
        (
            "(+",
            OperatorName,
            vec![(LParen, 17..18), (Operator, 18..19), (Missing, 19..19)],
            Some((Missing, 19..19)),
        ),
    ] {
        let source = format!("use x::* without {text}");
        let end = source.len() as u32;
        let (green, _) = run_statement(&source);
        assert_eq!(green.to_string(), source);
        let declaration = use_declaration(&green);
        let exclusions: Vec<_> = declaration
            .descendants()
            .filter(|node| node.kind() == UseExclusion)
            .collect();
        let recursive = text == "{y::* without z}";
        assert_eq!(
            exclusions.len(),
            if recursive { 2 } else { 1 },
            "{source:?}"
        );
        let exclusion = &exclusions[0];
        assert_eq!(
            exclusion.text_range(),
            rowan::TextRange::new(17.into(), end.into())
        );
        assert_eq!(exclusion.to_string(), text);
        assert_eq!(
            exclusion
                .ancestors()
                .take(5)
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [UseExclusion, UseGlob, UseTree, UseDeclaration, Statement]
        );
        assert_eq!(
            projection(exclusion),
            [(payload_kind, 17..end)],
            "{source:?}"
        );
        // Dispatch owns one payload; the keyword and its gaps belong to UseGlob.
        let glob = exclusion.parent().unwrap();
        assert_eq!(
            projection(&glob),
            [
                (Star, 7..8),
                (Whitespace, 8..9),
                (WithoutKw, 9..16),
                (Whitespace, 16..17),
                (UseExclusion, 17..end)
            ]
        );
        let payload = exclusion.children_with_tokens().next().unwrap();
        assert_eq!(payload.parent().as_ref(), Some(exclusion));
        assert_eq!(
            payload.as_node().is_some(),
            matches!(payload_kind, OperatorName | UseExclusionGroup)
        );
        if let Some(node) = payload.as_node() {
            assert_eq!(projection(node), children, "{source:?}");
            for child in node.children_with_tokens() {
                assert_eq!(child.parent().as_ref(), Some(node));
                assert_eq!(
                    child.as_node().is_some(),
                    matches!(child.kind(), UseTree | Missing)
                );
            }
        } else {
            assert!(children.is_empty());
        }
        if recursive {
            let inner = &exclusions[1];
            assert_eq!(
                inner.text_range(),
                rowan::TextRange::new(31.into(), 32.into())
            );
            assert_eq!(inner.to_string(), "z");
            assert_eq!(projection(inner), [(Identifier, 31..32)]);
            let identifier = inner.children_with_tokens().next().unwrap();
            assert!(identifier.as_token().is_some());
            assert_eq!(identifier.parent().as_ref(), Some(inner));
            assert_eq!(
                inner
                    .ancestors()
                    .take(8)
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                [
                    UseExclusion,
                    UseGlob,
                    UseTree,
                    UseExclusionGroup,
                    UseExclusion,
                    UseGlob,
                    UseTree,
                    UseDeclaration
                ]
            );
            let inner_glob = inner.parent().unwrap();
            assert_eq!(
                projection(&inner_glob),
                [
                    (Star, 21..22),
                    (Whitespace, 22..23),
                    (WithoutKw, 23..30),
                    (Whitespace, 30..31),
                    (UseExclusion, 31..32)
                ]
            );
            let tree = inner_glob.parent().unwrap();
            assert_eq!(
                projection(&tree),
                [(UsePath, 18..19), (ColonColon, 19..21), (UseGlob, 21..32)]
            );
        }
        // These assertions read only Rowan topology and source ranges, including
        // delegated recovery; no diagnostic belongs to the dispatcher itself.
        for child in declaration.descendants_with_tokens() {
            let range = child.text_range();
            assert_eq!(
                child.to_string(),
                source[usize::from(range.start())..usize::from(range.end())]
            );
            assert!(!matches!(child.kind(), Invalid | UseGroupForeignClose));
        }
        let recoveries: Vec<_> = declaration
            .descendants_with_tokens()
            .filter(|child| matches!(child.kind(), Error | Missing))
            .collect();
        assert_eq!(
            recoveries.len(),
            usize::from(recovery.is_some()),
            "{source:?}"
        );
        if let Some((kind, range)) = recovery {
            let child = &recoveries[0];
            assert_eq!(child.kind(), kind);
            assert_eq!(
                child.text_range(),
                rowan::TextRange::new(range.start.into(), range.end.into())
            );
            assert_eq!(child.parent().as_ref(), payload.as_node());
            assert_eq!(child.as_node().is_some(), kind == Missing);
            if let Some(missing) = child.as_node() {
                assert!(missing.text_range().is_empty());
                assert!(missing.children_with_tokens().next().is_none());
            }
        }
    }
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
fn use_path_frames_balance_at_required_segment_exits() {
    use SyntaxKind::*;
    use std::sync::Arc;

    for (text, path_text, missing) in [
        ("use 猫::", "猫::", true),
        ("use 猫:: \r\n", "猫::", true),
        ("use 猫/", "猫/", true),
        ("use realm/", "", true),
        ("use band::", "", true),
        ("use 猫::q", "猫::q", false),
        ("use 猫::{q}", "猫", false),
        ("use 猫::*", "猫", false),
    ] {
        let source: Arc<crate::SourceText> = Arc::from(text);
        let header = Arc::new(crate::scan_header(Arc::clone(&source)));
        let fresh = crate::cursor::parse_root(text, &OperatorTable::empty(), &[]);
        let parsed = crate::parse_file(
            source,
            Arc::clone(&header),
            Arc::new(crate::SyntaxEnvironment::empty()),
        );
        assert_eq!(parsed.green(), &fresh.green, "{text:?}");
        assert_eq!(
            fresh.committed_recoveries.as_slice(),
            header.recoveries.as_ref(),
            "{text:?}"
        );
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(root.kind(), Root, "{text:?}");
        assert_eq!(root.to_string(), text);
        let path = root
            .descendants()
            .find(|node| node.kind() == UsePath)
            .unwrap();
        assert_eq!(path.to_string(), path_text);
        assert_eq!(
            path.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
            [UsePath, UseTree, UseDeclaration, Root]
        );
        let missing_nodes = root
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect::<Vec<_>>();
        assert_eq!(missing_nodes.len(), usize::from(missing));
        if missing {
            assert_eq!(missing_nodes[0].parent(), Some(path.clone()));
            assert!(missing_nodes[0].text_range().is_empty());
            assert_eq!(
                missing_nodes[0].text_range().start(),
                path.text_range().end()
            );
        }
    }

    for prefix in ["use 猫::", "use 猫/", "use realm/", "use band::"] {
        for pending in ["\r\n;next", " )next"] {
            let source = format!("{prefix}{pending}");
            let mut input = source.as_str();
            let operators = OperatorTable::empty();
            let mut recover = Recover::new_for_test(&operators);
            let mut builder = GreenNodeBuilder::new();
            builder.start_node(Root.into());
            let exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
            builder.finish_node();
            let root = SyntaxNode::new_root(builder.finish());
            assert_eq!(root.kind(), Root, "{source:?}");
            assert_eq!(root.to_string(), prefix);
            let Err(Either::Left(mut item)) = exit else {
                panic!("protected boundary must remain pending: {source:?}");
            };
            let spelling = item.payload_view().spelling().unwrap().to_owned();
            let leading = emit_pending_leading_text(&mut item);
            assert_eq!(format!("{root}{leading}{spelling}{input}"), source);
            assert_eq!(input, "next");
            assert_eq!(recover.finish_recoveries_for_test().len(), 1);
        }
    }
}

#[test]
fn use_mod_path_frames_balance_at_required_word_exits() {
    use SyntaxKind::*;
    use std::sync::Arc;

    for (text, path_text) in [
        ("use mod @", " @"),
        ("use mod @;next", " @"),
        ("use mod @\nnext", " @"),
        ("use mod p", "p"),
        ("use mod p;next", "p"),
        ("use mod p\nnext", "p"),
        ("use mod p::q", "p::q"),
    ] {
        let source: Arc<crate::SourceText> = Arc::from(text);
        let header = Arc::new(crate::scan_header(Arc::clone(&source)));
        let fresh = crate::cursor::parse_root(text, &OperatorTable::empty(), &[]);
        let parsed = crate::parse_file(
            source,
            Arc::clone(&header),
            Arc::new(crate::SyntaxEnvironment::empty()),
        );
        assert_eq!(parsed.green(), &fresh.green, "{text:?}");
        assert_eq!(
            fresh.committed_recoveries.as_slice(),
            header.recoveries.as_ref(),
            "{text:?}"
        );
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(root.kind(), Root, "{text:?}");
        assert_eq!(root.to_string(), text);
        let path = root
            .descendants()
            .find(|node| node.kind() == UsePath)
            .unwrap();
        assert_eq!(path.to_string(), path_text, "{text:?}");
        assert_eq!(
            path.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
            [UsePath, UseTree, UseDeclaration, Root],
            "{text:?}"
        );
        if text.ends_with("next") {
            assert!(root.children().any(|node| node.to_string() == "next"));
        }
    }
}

#[test]
fn use_schema_required_path_segment_direct_occurrences() {
    use SyntaxKind::*;

    // Only nonterminal separators under UseTree > UsePath select these
    // Import(Path)/Path slots. Anchor paths and terminal joins have other owners.
    for (separator, kind, next_separator, next_kind) in [
        ("::", ColonColon, "/", Slash),
        ("/", Slash, "::", ColonColon),
    ] {
        let start = 7 + separator.len() as u32;
        for (suffix, children, occurrences, pending) in [
            ("q".to_owned(), vec![(Identifier, "q")], vec![], ""),
            ("(+)".to_owned(), vec![(OperatorName, "(+)")], vec![], ""),
            (
                "".to_owned(),
                vec![(Missing, "")],
                vec![(Missing, start..start)],
                "",
            ),
            (
                "@ #".to_owned(),
                vec![(Error, "@"), (Error, " "), (Error, "#")],
                vec![(Error, start..start + 3)],
                "",
            ),
            (
                "@ # q".to_owned(),
                vec![
                    (Error, "@"),
                    (Error, " "),
                    (Error, "#"),
                    (Whitespace, " "),
                    (Identifier, "q"),
                ],
                vec![(Error, start..start + 3)],
                "",
            ),
            (
                "@ (+)".to_owned(),
                vec![(Error, "@"), (Whitespace, " "), (OperatorName, "(+)")],
                vec![(Error, start..start + 1)],
                "",
            ),
            (
                "".to_owned(),
                vec![(Missing, "")],
                vec![(Missing, start..start)],
                " ;next",
            ),
            (
                "@ #".to_owned(),
                vec![(Error, "@"), (Error, " "), (Error, "#")],
                vec![(Error, start..start + 3)],
                " ;next",
            ),
            (
                "".to_owned(),
                vec![(Missing, "")],
                vec![(Missing, start..start)],
                "\r\n;next",
            ),
            (
                "@ #".to_owned(),
                vec![(Error, "@"), (Error, " "), (Error, "#")],
                vec![(Error, start..start + 3)],
                "\r\n;next",
            ),
            (
                format!("@ q{next_separator}@ # r"),
                vec![
                    (Error, "@"),
                    (Whitespace, " "),
                    (Identifier, "q"),
                    (next_kind, next_separator),
                    (Error, "@"),
                    (Error, " "),
                    (Error, "#"),
                    (Whitespace, " "),
                    (Identifier, "r"),
                ],
                vec![
                    (Error, start..start + 1),
                    (
                        Error,
                        start + 3 + next_separator.len() as u32
                            ..start + 6 + next_separator.len() as u32,
                    ),
                ],
                "",
            ),
        ] {
            let source = format!("use 猫{separator}{suffix}{pending}");
            let mut expected = vec![(Identifier, "猫"), (kind, separator)];
            expected.extend(children);
            let operators = OperatorTable::empty();
            let mut previous: Option<(GreenNode, Vec<CommittedRecoveryRecord>)> = None;
            for _ in 0..2 {
                let mut input = source.as_str();
                let mut recover = match &previous {
                    Some((_, records)) => Recover::reconcile_for_test(&operators, records),
                    None => Recover::new_for_test(&operators),
                };
                let mut builder = GreenNodeBuilder::new();
                builder.start_node(Root.into());
                let mut exit =
                    statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
                if let Err(Either::Right(end)) = &mut exit {
                    emit_end(&mut builder, end);
                }
                builder.finish_node();
                let green = builder.finish();
                let records = recover.finish_recoveries_for_test();
                let root = SyntaxNode::new_root(green.clone());
                let path = root
                    .descendants()
                    .find(|node| node.kind() == UsePath)
                    .unwrap();
                assert_eq!(
                    path.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
                    [UsePath, UseTree, UseDeclaration, Statement, Root],
                    "{source:?}: {root:#?}"
                );
                assert_use_composition_children(&path, 4, &expected);
                let mut actual = Vec::new();
                let mut run: Option<std::ops::Range<u32>> = None;
                for child in path.children_with_tokens() {
                    assert_eq!(
                        child.as_node().is_some(),
                        matches!(child.kind(), Missing | OperatorName)
                    );
                    let range = child.text_range();
                    if child.kind() == Error {
                        if let Some(run) = &mut run {
                            assert_eq!(run.end, u32::from(range.start()));
                            run.end = u32::from(range.end());
                        } else {
                            run = Some(u32::from(range.start())..u32::from(range.end()));
                        }
                    } else {
                        if let Some(run) = run.take() {
                            actual.push((Error, run));
                        }
                        if child.kind() == Missing {
                            assert!(range.is_empty());
                            assert!(
                                child
                                    .as_node()
                                    .unwrap()
                                    .children_with_tokens()
                                    .next()
                                    .is_none()
                            );
                            actual
                                .push((Missing, u32::from(range.start())..u32::from(range.end())));
                        }
                    }
                }
                if let Some(run) = run {
                    actual.push((Error, run));
                }
                assert_eq!(actual, occurrences, "{source:?}");
                for child in root.descendants_with_tokens() {
                    let range = child.text_range();
                    assert_eq!(
                        child.to_string(),
                        source[usize::from(range.start())..usize::from(range.end())]
                    );
                    assert!(!matches!(child.kind(), Invalid | UseGroupForeignClose));
                    if matches!(child.kind(), Missing | Error) {
                        assert_eq!(child.parent().as_ref(), Some(&path));
                    }
                }
                if pending.is_empty() {
                    assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
                    assert_eq!(input, "");
                    assert_eq!(root.to_string(), source);
                } else {
                    let end = (start as usize) + suffix.len();
                    let leading_len = pending.find(';').unwrap();
                    assert_eq!(root.to_string(), source[..end]);
                    let Err(Either::Left(mut item)) = exit else {
                        panic!("protected semicolon must remain pending: {source:?}")
                    };
                    assert_eq!(token_kind(&item), Some(TokenKind::Semicolon));
                    assert_eq!(item.payload_view().spelling(), Some(";"));
                    let extent = item.extent(source.len() - input.len());
                    assert_eq!(extent.leading(), end..end + leading_len);
                    assert_eq!(extent.payload(), end + leading_len..end + leading_len + 1);
                    let leading = emit_pending_leading_text(&mut item);
                    assert_eq!(leading, pending[..leading_len]);
                    assert_eq!(input, "next");
                    assert_eq!(format!("{root}{leading};{input}"), source);
                }
                if let Some((fresh, fresh_records)) = &previous {
                    assert_eq!(&green, fresh, "{source:?}");
                    assert_eq!(&records, fresh_records, "{source:?}");
                } else {
                    previous = Some((green, records));
                }
            }
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
    // Initial Missing before Comma projects Import(GroupEntry)/Path; after a
    // child, Missing before the next UseTree projects Import(GroupEntry)/Comma.
    // Neither occurrence is the local terminal-close slot.
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
        (
            "use x::* without (, )",
            vec![
                (LParen, 17..18),
                (Missing, 18..18),
                (Comma, 18..19),
                (Whitespace, 19..20),
                (RParen, 20..21),
            ],
        ),
        (
            "use x::* without (a b)",
            vec![
                (LParen, 17..18),
                (UseTree, 18..19),
                (Whitespace, 19..20),
                (Missing, 20..20),
                (UseTree, 20..21),
                (RParen, 21..22),
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
        let (green, _) = run_statement(source);
        let declaration = use_declaration(&green);
        let group = declaration
            .descendants()
            .find(|node| node.kind() == UseExclusionGroup)
            .unwrap();
        assert!(group.children_with_tokens().all(|child| {
            child.parent().as_ref() == Some(&group)
                && child.as_node().is_some() == matches!(child.kind(), Missing | UseTree)
        }));
        let missing: Vec<_> = declaration
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect();
        assert_eq!(missing.len(), 1, "{source:?}");
        assert_eq!(missing[0].parent().as_ref(), Some(&group));
        assert!(missing[0].text_range().is_empty());
        assert!(missing[0].children_with_tokens().next().is_none());
        assert!(
            !declaration
                .descendants_with_tokens()
                .any(|child| matches!(child.kind(), Error | Invalid)),
            "{source:?}"
        );
    }
}

#[test]
fn use_schema_group_entry_raw_error_runs() {
    use SyntaxKind::*;

    for (prefix, owner, open, close, closing, foreign) in [
        ("use ", UseGroup, LBrace, RBrace, '}', ')'),
        (
            "use x::* without ",
            UseExclusionGroup,
            LBrace,
            RBrace,
            '}',
            ')',
        ),
        (
            "use x::* without ",
            UseExclusionGroup,
            LParen,
            RParen,
            ')',
            '}',
        ),
    ] {
        let start = prefix.len() as u32;
        // Whitespace prevents the parenthesized exclusion from selecting an
        // OperatorName; the following Error belongs to the group-entry slot.
        let (opening, leading) = if open == LParen {
            ('(', " ")
        } else {
            ('{', "")
        };
        let body = start + 1 + leading.len() as u32;
        let ancestors = if owner == UseGroup {
            vec![UseGroup, UseTree, UseDeclaration, Statement]
        } else {
            vec![
                UseExclusionGroup,
                UseExclusion,
                UseGlob,
                UseTree,
                UseDeclaration,
                Statement,
            ]
        };
        for (text, children, error_range) in [
            (
                "@".to_owned(),
                vec![(Error, body..body + 1)],
                body..body + 1,
            ),
            (
                "@a".to_owned(),
                vec![(Error, body..body + 1), (UseTree, body + 1..body + 2)],
                body..body + 1,
            ),
            (
                "@,a".to_owned(),
                vec![
                    (Error, body..body + 1),
                    (Comma, body + 1..body + 2),
                    (UseTree, body + 2..body + 3),
                ],
                body..body + 1,
            ),
            (
                format!("@{foreign}"),
                vec![(Error, body..body + 1), (Error, body + 1..body + 2)],
                body..body + 2,
            ),
            (
                "/*é*/ @".to_owned(),
                vec![
                    (BlockComment, body..body + 6),
                    (Whitespace, body + 6..body + 7),
                    (Error, body + 7..body + 8),
                ],
                body + 7..body + 8,
            ),
            (
                "@ /*é*/ a".to_owned(),
                vec![
                    (Error, body..body + 1),
                    (Whitespace, body + 1..body + 2),
                    (BlockComment, body + 2..body + 8),
                    (Whitespace, body + 8..body + 9),
                    (UseTree, body + 9..body + 10),
                ],
                body..body + 1,
            ),
        ] {
            let source = format!("{prefix}{opening}{leading}{text}{closing}");
            let end = body + text.len() as u32;
            let mut expected = vec![(open, start..start + 1)];
            if !leading.is_empty() {
                expected.push((Whitespace, start + 1..body));
            }
            expected.extend(children);
            expected.push((close, end..end + 1));
            assert_use_schema_children(&source, owner, &ancestors, &expected);

            let (green, _) = run_statement(&source);
            assert_eq!(green.to_string(), source);
            let declaration = use_declaration(&green);
            let group = declaration
                .descendants()
                .find(|node| node.kind() == owner)
                .unwrap();
            assert!(
                group
                    .descendants_with_tokens()
                    .all(|child| !matches!(child.kind(), Missing | Invalid | UseGroupForeignClose)),
                "{source:?}"
            );
            let mut runs = Vec::new();
            let mut current: Option<std::ops::Range<u32>> = None;
            for child in group.children_with_tokens() {
                assert_eq!(child.parent().as_ref(), Some(&group));
                assert_eq!(child.as_node().is_some(), child.kind() == UseTree);
                let range = child.text_range();
                assert_eq!(
                    child.to_string(),
                    source[usize::from(range.start())..usize::from(range.end())]
                );
                if child.kind() == Error {
                    // Grouping uses only adjacency and the immediate owner,
                    // never the opaque malformed spelling or recovery ledger.
                    let end = u32::from(range.end());
                    if let Some(run) = &mut current {
                        assert_eq!(run.end, u32::from(range.start()));
                        run.end = end;
                    } else {
                        current = Some(u32::from(range.start())..end);
                    }
                } else if let Some(run) = current.take() {
                    runs.push(run);
                }
            }
            if let Some(run) = current {
                runs.push(run);
            }
            assert_eq!(runs, vec![error_range], "{source:?}");
        }
    }
}

#[test]
fn use_schema_post_child_group_entry_raw_error_runs() {
    use SyntaxKind::*;

    for (prefix, owner, open, close, opening, closing, foreign) in [
        ("use ", UseGroup, LBrace, RBrace, '{', '}', ')'),
        (
            "use x::* without ",
            UseExclusionGroup,
            LBrace,
            RBrace,
            '{',
            '}',
            ')',
        ),
        (
            "use x::* without ",
            UseExclusionGroup,
            LParen,
            RParen,
            '(',
            ')',
            '}',
        ),
    ] {
        let start = prefix.len() as u32;
        let body = start + 1;
        // The admitted identifier also prevents the parenthesized exclusion
        // from selecting OperatorName. Raw recovery preserves after_child;
        // only the native comma clears the separator requirement on retry.
        for (text, children, error_range, missing_at, protected) in [
            (
                "a@".to_owned(),
                vec![(Error, body + 1..body + 2)],
                body + 1..body + 2,
                None,
                false,
            ),
            (
                "a@b".to_owned(),
                vec![
                    (Error, body + 1..body + 2),
                    (Missing, body + 2..body + 2),
                    (UseTree, body + 2..body + 3),
                ],
                body + 1..body + 2,
                Some(body + 2),
                false,
            ),
            (
                "a@,b".to_owned(),
                vec![
                    (Error, body + 1..body + 2),
                    (Comma, body + 2..body + 3),
                    (UseTree, body + 3..body + 4),
                ],
                body + 1..body + 2,
                None,
                false,
            ),
            (
                format!("a@{foreign}"),
                vec![(Error, body + 1..body + 2), (Error, body + 2..body + 3)],
                body + 1..body + 3,
                None,
                false,
            ),
            (
                "a /*é*/ @".to_owned(),
                vec![
                    (Whitespace, body + 1..body + 2),
                    (BlockComment, body + 2..body + 8),
                    (Whitespace, body + 8..body + 9),
                    (Error, body + 9..body + 10),
                ],
                body + 9..body + 10,
                None,
                false,
            ),
            (
                "a@ /*é*/ b".to_owned(),
                vec![
                    (Error, body + 1..body + 2),
                    (Whitespace, body + 2..body + 3),
                    (BlockComment, body + 3..body + 9),
                    (Whitespace, body + 9..body + 10),
                    (Missing, body + 10..body + 10),
                    (UseTree, body + 10..body + 11),
                ],
                body + 1..body + 2,
                Some(body + 10),
                false,
            ),
            (
                "a@ ;next".to_owned(),
                vec![(Error, body + 1..body + 2)],
                body + 1..body + 2,
                None,
                true,
            ),
        ] {
            let suffix = if protected {
                String::new()
            } else {
                closing.to_string()
            };
            let source = format!("{prefix}{opening}{text}{suffix}");
            let mut expected = vec![(open, start..body), (UseTree, body..body + 1)];
            expected.extend(children);
            if !protected {
                let end = body + text.len() as u32;
                expected.push((close, end..end + 1));
            }
            let operators = OperatorTable::empty();
            let mut input = source.as_str();
            let mut recover = Recover::new_for_test(&operators);
            let mut builder = GreenNodeBuilder::new();
            builder.start_node(Root.into());
            let mut exit = statement(SyntaxIn::new(&mut input, &mut recover, &mut builder), 0, 0);
            if let Err(Either::Right(end)) = &mut exit {
                emit_end(&mut builder, end);
            }
            builder.finish_node();
            let root = SyntaxNode::new_root(finish_with_discarded_recoveries(builder, recover));
            let group = root
                .descendants()
                .find(|node| node.kind() == owner)
                .unwrap();
            let ancestors = if owner == UseGroup {
                vec![UseGroup, UseTree, UseDeclaration, Statement, Root]
            } else {
                vec![
                    UseExclusionGroup,
                    UseExclusion,
                    UseGlob,
                    UseTree,
                    UseDeclaration,
                    Statement,
                    Root,
                ]
            };
            assert_eq!(
                group
                    .ancestors()
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                ancestors
            );
            assert_eq!(
                group
                    .children_with_tokens()
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
            assert!(
                !root
                    .descendants_with_tokens()
                    .any(|child| matches!(child.kind(), Invalid | UseGroupForeignClose))
            );
            let missing: Vec<_> = root
                .descendants()
                .filter(|node| node.kind() == Missing)
                .collect();
            assert_eq!(
                missing.len(),
                usize::from(missing_at.is_some()),
                "{source:?}"
            );
            if let Some(at) = missing_at {
                assert_eq!(missing[0].parent().as_ref(), Some(&group));
                assert_eq!(missing[0].text_range(), rowan::TextRange::empty(at.into()));
                assert!(missing[0].children_with_tokens().next().is_none());
            }
            let mut runs = Vec::new();
            let mut current: Option<std::ops::Range<u32>> = None;
            for child in group.children_with_tokens() {
                assert_eq!(child.parent().as_ref(), Some(&group));
                assert_eq!(
                    child.as_node().is_some(),
                    matches!(child.kind(), UseTree | Missing)
                );
                let range = child.text_range();
                assert_eq!(
                    child.to_string(),
                    source[usize::from(range.start())..usize::from(range.end())]
                );
                // The occurrence uses only direct adjacency, never Error spelling.
                if child.kind() == Error {
                    if let Some(run) = &mut current {
                        assert_eq!(run.end, u32::from(range.start()));
                        run.end = u32::from(range.end());
                    } else {
                        current = Some(u32::from(range.start())..u32::from(range.end()));
                    }
                } else if let Some(run) = current.take() {
                    runs.push(run);
                }
            }
            if let Some(run) = current {
                runs.push(run);
            }
            assert_eq!(runs, vec![error_range], "{source:?}");
            if protected {
                assert_eq!(root.to_string(), source[..(body + 2) as usize]);
                let Err(Either::Left(mut item)) = exit else {
                    panic!("protected semicolon must remain pending")
                };
                assert_eq!(token_kind(&item), Some(TokenKind::Semicolon));
                assert_eq!(item.payload_view().spelling(), Some(";"));
                let extent = item.extent(source.len() - input.len());
                assert_eq!(extent.leading(), (body + 2) as usize..(body + 3) as usize);
                assert_eq!(extent.payload(), (body + 3) as usize..(body + 4) as usize);
                assert_eq!(emit_pending_leading_text(&mut item), " ");
                assert_eq!(input, "next");
                assert_eq!(format!("{root} ;{input}"), source);
            } else {
                assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
                assert_eq!(input, "");
                assert_eq!(root.to_string(), source);
            }
        }
    }
}

#[test]
fn use_schema_group_local_terminal_close_phases() {
    use SyntaxKind::*;
    for (prefix, owner, open, close, closing, foreign) in [
        ("use ", UseGroup, LBrace, RBrace, '}', ')'),
        (
            "use x::* without ",
            UseExclusionGroup,
            LBrace,
            RBrace,
            '}',
            ')',
        ),
        (
            "use x::* without ",
            UseExclusionGroup,
            LParen,
            RParen,
            ')',
            '}',
        ),
    ] {
        let start = prefix.len() as u32;
        let body = start + 1;
        let opening = if open == LBrace { '{' } else { '(' };
        let ancestors = if owner == UseGroup {
            vec![UseGroup, UseTree, UseDeclaration, Statement]
        } else {
            vec![
                UseExclusionGroup,
                UseExclusion,
                UseGlob,
                UseTree,
                UseDeclaration,
                Statement,
            ]
        };
        // These are local terminal episodes, not a claim that every group exit
        // produces a close Missing. Earlier entry/separator Missing nodes are
        // distinguished by the following Comma or UseTree.
        for (text, children) in [
            (String::new(), vec![]),
            ("猫".into(), vec![(UseTree, body..body + 3)]),
            (
                "a,".into(),
                vec![(UseTree, body..body + 1), (Comma, body + 1..body + 2)],
            ),
            (
                ",".into(),
                vec![(Missing, body..body), (Comma, body..body + 1)],
            ),
            (
                "a b".into(),
                vec![
                    (UseTree, body..body + 1),
                    (Whitespace, body + 1..body + 2),
                    (Missing, body + 2..body + 2),
                    (UseTree, body + 2..body + 3),
                ],
            ),
            (
                foreign.to_string(),
                vec![(UseGroupForeignClose, body..body + 1)],
            ),
        ] {
            let end = body + text.len() as u32;
            for matched in [false, true] {
                let mut expected = vec![(open, start..body)];
                expected.extend(children.clone());
                expected.push(if matched {
                    (close, end..end + 1)
                } else {
                    (Missing, end..end)
                });
                let suffix = if matched {
                    closing.to_string()
                } else {
                    String::new()
                };
                assert_use_schema_children(
                    &format!("{prefix}{opening}{text}{suffix}"),
                    owner,
                    &ancestors,
                    &expected,
                );
            }
        }
    }
}

#[test]
fn use_schema_group_local_close_preserves_pending_crlf_leading() {
    use SyntaxKind::*;
    for (prefix, owner, open) in [
        ("use {", UseGroup, LBrace),
        ("use x::* without {", UseExclusionGroup, LBrace),
        ("use x::* without (", UseExclusionGroup, LParen),
    ] {
        let body = prefix.len() as u32;
        let accepted = format!("{prefix}猫,");
        let (green, exit) = run_statement(&format!("{accepted}\r\nuse b"));
        assert_eq!(green.to_string(), accepted);
        let declaration = use_declaration(&green);
        let group = declaration
            .descendants()
            .find(|node| node.kind() == owner)
            .unwrap();
        assert_eq!(
            group.parent().unwrap().kind(),
            if owner == UseGroup {
                UseTree
            } else {
                UseExclusion
            }
        );
        assert_eq!(
            group
                .children_with_tokens()
                .map(|child| {
                    let range = child.text_range();
                    (
                        child.kind(),
                        u32::from(range.start())..u32::from(range.end()),
                    )
                })
                .collect::<Vec<_>>(),
            vec![
                (open, body - 1..body),
                (UseTree, body..body + 3),
                (Comma, body + 3..body + 4),
                (Missing, body + 4..body + 4),
            ]
        );
        let Some(Err(Either::Left(mut item))) = exit else {
            panic!("caller intro must remain pending")
        };
        assert_eq!(item.payload_view().spelling(), Some("use"));
        assert_eq!(emit_pending_leading_text(&mut item), "\r\n");
    }
}

#[test]
fn use_schema_group_local_close_borrows_outer_close_after_leading() {
    use SyntaxKind::*;
    assert_use_schema_children(
        "use {x::* without (a  }",
        UseGroup,
        &[UseGroup, UseTree, UseDeclaration, Statement],
        &[(LBrace, 4..5), (UseTree, 5..22), (RBrace, 22..23)],
    );
    assert_use_schema_children(
        "use {x::* without (a  }",
        UseExclusionGroup,
        &[UseExclusionGroup, UseExclusion, UseGlob, UseTree, UseGroup],
        &[
            (LParen, 18..19),
            (UseTree, 19..20),
            (Whitespace, 20..22),
            (Missing, 22..22),
        ],
    );
    assert_use_schema_occurrence(
        "use x::* without ({a  )",
        UseGroup,
        0,
        &[UseGroup, UseTree, UseExclusionGroup, UseExclusion, UseGlob],
        &[
            (LBrace, 18..19),
            (UseTree, 19..20),
            (Whitespace, 20..22),
            (Missing, 22..22),
        ],
    );
    assert_use_schema_children(
        "use x::* without ({a  )",
        UseExclusionGroup,
        &[UseExclusionGroup, UseExclusion, UseGlob, UseTree],
        &[(LParen, 17..18), (UseTree, 18..22), (RParen, 22..23)],
    );
}

#[test]
fn use_schema_group_propagated_exits_have_no_local_close_missing() {
    use SyntaxKind::*;
    for (source, expected) in [
        ("use {a::", vec![(LBrace, 4..5), (UseTree, 5..8)]),
        ("use {@", vec![(LBrace, 4..5), (Error, 5..6)]),
    ] {
        assert_use_schema_children(
            source,
            UseGroup,
            &[UseGroup, UseTree, UseDeclaration, Statement],
            &expected,
        );
    }
    assert_use_schema_children(
        "use {a::",
        UsePath,
        &[UsePath, UseTree, UseGroup],
        &[(Identifier, 5..6), (ColonColon, 6..8), (Missing, 8..8)],
    );
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
            descendants_of_kind(&declaration, SyntaxKind::UseGroupForeignClose),
            1
        );
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
    assert_eq!(
        descendants_of_kind(&declaration, SyntaxKind::UseGroupForeignClose),
        0
    );
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
    assert_eq!(
        descendants_of_kind(&use_declaration(&green), SyntaxKind::UseGroupForeignClose),
        0
    );
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

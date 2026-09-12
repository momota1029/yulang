use crate::tests::support::*;

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

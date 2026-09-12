use crate::declaration::declaration_variant::{VariantOwner, declaration_variant_owner_witness};
use crate::recovery_record::{
    ConstructRole, DeclarationRole, Delimiter, DiagnosticId, EnumDeclarationRole,
    ErrorDeclarationRole, ExpectationSources, ExpectedSyntax, GrammarRole, PunctuationEvidence,
    RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    VariantDeclarationRole,
};
use crate::tests::support::*;
use std::sync::Arc;

#[test]
fn colon_indented_variant_sequence_composes_header_retries_and_body_occurrences() {
    use SyntaxKind::{
        Colon, EnumKw, EnumVariant, Error, ErrorKw, Identifier, Invalid, LParen, Missing, Newline,
        RParen, Root, Whitespace,
    };

    // Two owners × two header slots × four sequence classes × EOF/dedent.
    for (keyword, keyword_kind, declaration) in [
        ("enum", EnumKw, SyntaxKind::EnumDeclaration),
        ("error", ErrorKw, SyntaxKind::ErrorDeclaration),
    ] {
        for (header, header_children, error_offset) in [
            (
                " @ 名 ",
                vec![
                    (Whitespace, 1),
                    (Error, 1),
                    (Whitespace, 1),
                    (Identifier, 3),
                    (Whitespace, 1),
                ],
                1,
            ),
            (
                " 名 @ ",
                vec![
                    (Whitespace, 1),
                    (Identifier, 3),
                    (Whitespace, 1),
                    (Error, 1),
                    (Whitespace, 1),
                ],
                5,
            ),
        ] {
            for dedent in [false, true] {
                for (body, sequence, variants) in [
                    (
                        "\n  A\n  B",
                        vec![
                            (EnumVariant, 4),
                            (Newline, 1),
                            (Whitespace, 2),
                            (EnumVariant, 1),
                        ],
                        vec![
                            vec![(Newline, 1), (Whitespace, 2), (Identifier, 1)],
                            vec![(Identifier, 1)],
                        ],
                    ),
                    (
                        "\n  @",
                        vec![(EnumVariant, 4)],
                        vec![vec![(Newline, 1), (Whitespace, 2), (Error, 1)]],
                    ),
                    (
                        "\n  @ A",
                        vec![(EnumVariant, 6)],
                        vec![vec![
                            (Newline, 1),
                            (Whitespace, 2),
                            (Error, 1),
                            (Whitespace, 1),
                            (Identifier, 1),
                        ]],
                    ),
                    (
                        "\n  A()B",
                        vec![(EnumVariant, 6), (Missing, 0), (EnumVariant, 1)],
                        vec![
                            vec![
                                (Newline, 1),
                                (Whitespace, 2),
                                (Identifier, 1),
                                (LParen, 1),
                                (RParen, 1),
                            ],
                            vec![(Identifier, 1)],
                        ],
                    ),
                ] {
                    let accepted = format!("{keyword}{header}:{body}");
                    let source = format!("{accepted}{}", if dedent { "\nnext" } else { "" });
                    let (green, exit, remainder) = if declaration == SyntaxKind::EnumDeclaration {
                        run_enum_declaration(&source, 0, 100, LineEntry::InLine, None)
                    } else {
                        run_error_declaration(&source, 0, 100, LineEntry::InLine, None)
                    };
                    assert_eq!(remainder, "", "{source:?}");
                    let root = syntax_root(green);
                    assert_eq!(root.kind(), Root);
                    assert!(root.parent().is_none());
                    assert_eq!(root.children_with_tokens().count(), 1);
                    assert_eq!(root.to_string(), accepted);
                    let shell = root.children().next().unwrap();
                    assert_eq!(shell.kind(), declaration);
                    assert_eq!(shell.parent().as_ref(), Some(&root));
                    assert_eq!(shell.text_range(), root.text_range());
                    let mut expected = vec![(keyword_kind, keyword.len())];
                    expected.extend_from_slice(&header_children);
                    expected.push((Colon, 1));
                    expected.extend_from_slice(&sequence);
                    assert_variant_sequence_children(&shell, 0, &expected, &source);
                    let actual_variants = shell
                        .children()
                        .filter(|node| node.kind() == EnumVariant)
                        .collect::<Vec<_>>();
                    assert_eq!(actual_variants.len(), variants.len());
                    for (variant, children) in actual_variants.iter().zip(&variants) {
                        assert_variant_sequence_children(
                            variant,
                            usize::from(variant.text_range().start()),
                            children,
                            &source,
                        );
                    }
                    let start = keyword.len() + header.len() + 1;
                    let header_error = keyword.len() + error_offset;
                    let mut occurrences =
                        vec![(Error, declaration, header_error..header_error + 1)];
                    match body {
                        "\n  @" | "\n  @ A" => {
                            occurrences.push((Error, EnumVariant, start + 3..start + 4))
                        }
                        "\n  A()B" => {
                            occurrences.push((Missing, declaration, start + 6..start + 6))
                        }
                        _ => {}
                    }
                    let actual = root
                        .descendants_with_tokens()
                        .filter(|child| matches!(child.kind(), Error | Missing | Invalid))
                        .map(|child| {
                            (
                                child.kind(),
                                child.parent().unwrap().kind(),
                                usize::from(child.text_range().start())
                                    ..usize::from(child.text_range().end()),
                            )
                        })
                        .collect::<Vec<_>>();
                    assert_eq!(actual, occurrences, "{source:?}");
                    if dedent {
                        let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), _)) = exit
                        else {
                            panic!("dedent must remain pending: {source:?}")
                        };
                        assert_eq!(item.payload_view().spelling(), Some("next"));
                        let leading = emit_pending_leading_text(&mut item);
                        assert_eq!(leading, "\n");
                        assert_eq!(
                            format!(
                                "{root}{leading}{}{remainder}",
                                item.payload_view().spelling().unwrap()
                            ),
                            source
                        );
                    } else {
                        let Some(NormalizedExit::Complete(Err(Either::Right(mut end)), _)) = exit
                        else {
                            panic!("EOF must remain terminal: {source:?}")
                        };
                        assert!(end.item.payload_view().is_eof());
                        assert_eq!(emit_pending_leading_text(&mut end.item), "");
                        assert_eq!(root.to_string(), source);
                    }
                }
            }
        }
    }
}

#[test]
fn equals_indented_variant_sequence_composes_header_retries_and_body_occurrences() {
    use SyntaxKind::{
        EnumKw, EnumVariant, Equals, Error, ErrorKw, Identifier, Invalid, LParen, Missing, Newline,
        RParen, Root, Whitespace,
    };

    // Two owners × two header slots × four sequence classes × EOF/dedent.
    for (keyword, keyword_kind, declaration) in [
        ("enum", EnumKw, SyntaxKind::EnumDeclaration),
        ("error", ErrorKw, SyntaxKind::ErrorDeclaration),
    ] {
        for (header, header_children, error_offset) in [
            (
                " @ 名 ",
                vec![
                    (Whitespace, 1),
                    (Error, 1),
                    (Whitespace, 1),
                    (Identifier, 3),
                    (Whitespace, 1),
                ],
                1,
            ),
            (
                " 名 @ ",
                vec![
                    (Whitespace, 1),
                    (Identifier, 3),
                    (Whitespace, 1),
                    (Error, 1),
                    (Whitespace, 1),
                ],
                5,
            ),
        ] {
            for dedent in [false, true] {
                for (body, sequence, variants) in [
                    (
                        "\n  A\n  B",
                        vec![
                            (EnumVariant, 4),
                            (Newline, 1),
                            (Whitespace, 2),
                            (EnumVariant, 1),
                        ],
                        vec![
                            vec![(Newline, 1), (Whitespace, 2), (Identifier, 1)],
                            vec![(Identifier, 1)],
                        ],
                    ),
                    (
                        "\n  @",
                        vec![(EnumVariant, 4)],
                        vec![vec![(Newline, 1), (Whitespace, 2), (Error, 1)]],
                    ),
                    (
                        "\n  @ A",
                        vec![(EnumVariant, 6)],
                        vec![vec![
                            (Newline, 1),
                            (Whitespace, 2),
                            (Error, 1),
                            (Whitespace, 1),
                            (Identifier, 1),
                        ]],
                    ),
                    (
                        "\n  A()B",
                        vec![(EnumVariant, 6), (Missing, 0), (EnumVariant, 1)],
                        vec![
                            vec![
                                (Newline, 1),
                                (Whitespace, 2),
                                (Identifier, 1),
                                (LParen, 1),
                                (RParen, 1),
                            ],
                            vec![(Identifier, 1)],
                        ],
                    ),
                ] {
                    let accepted = format!("{keyword}{header}={body}");
                    let source = format!("{accepted}{}", if dedent { "\nnext" } else { "" });
                    let (green, exit, remainder) = if declaration == SyntaxKind::EnumDeclaration {
                        run_enum_declaration(&source, 0, 100, LineEntry::InLine, None)
                    } else {
                        run_error_declaration(&source, 0, 100, LineEntry::InLine, None)
                    };
                    assert_eq!(remainder, "", "{source:?}");
                    let root = syntax_root(green);
                    assert_eq!(root.kind(), Root);
                    assert!(root.parent().is_none());
                    assert_eq!(root.children_with_tokens().count(), 1);
                    assert_eq!(root.to_string(), accepted);
                    let shell = root.children().next().unwrap();
                    assert_eq!(shell.kind(), declaration);
                    assert_eq!(shell.parent().as_ref(), Some(&root));
                    assert_eq!(shell.text_range(), root.text_range());
                    let mut expected = vec![(keyword_kind, keyword.len())];
                    expected.extend_from_slice(&header_children);
                    expected.push((Equals, 1));
                    expected.extend_from_slice(&sequence);
                    assert_variant_sequence_children(&shell, 0, &expected, &source);
                    let actual_variants = shell
                        .children()
                        .filter(|node| node.kind() == EnumVariant)
                        .collect::<Vec<_>>();
                    assert_eq!(actual_variants.len(), variants.len());
                    for (variant, children) in actual_variants.iter().zip(&variants) {
                        assert_variant_sequence_children(
                            variant,
                            usize::from(variant.text_range().start()),
                            children,
                            &source,
                        );
                    }
                    let start = keyword.len() + header.len() + 1;
                    let header_error = keyword.len() + error_offset;
                    let mut occurrences =
                        vec![(Error, declaration, header_error..header_error + 1)];
                    match body {
                        "\n  @" | "\n  @ A" => {
                            occurrences.push((Error, EnumVariant, start + 3..start + 4))
                        }
                        "\n  A()B" => {
                            occurrences.push((Missing, declaration, start + 6..start + 6))
                        }
                        _ => {}
                    }
                    let actual = root
                        .descendants_with_tokens()
                        .filter(|child| matches!(child.kind(), Error | Missing | Invalid))
                        .map(|child| {
                            (
                                child.kind(),
                                child.parent().unwrap().kind(),
                                usize::from(child.text_range().start())
                                    ..usize::from(child.text_range().end()),
                            )
                        })
                        .collect::<Vec<_>>();
                    assert_eq!(actual, occurrences, "{source:?}");
                    if dedent {
                        let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), _)) = exit
                        else {
                            panic!("dedent must remain pending: {source:?}")
                        };
                        assert_eq!(item.payload_view().spelling(), Some("next"));
                        let leading = emit_pending_leading_text(&mut item);
                        assert_eq!(leading, "\n");
                        assert_eq!(
                            format!(
                                "{root}{leading}{}{remainder}",
                                item.payload_view().spelling().unwrap()
                            ),
                            source
                        );
                    } else {
                        let Some(NormalizedExit::Complete(Err(Either::Right(mut end)), _)) = exit
                        else {
                            panic!("EOF must remain terminal: {source:?}")
                        };
                        assert!(end.item.payload_view().is_eof());
                        assert_eq!(emit_pending_leading_text(&mut end.item), "");
                        assert_eq!(root.to_string(), source);
                    }
                }
            }
        }
    }
}

#[test]
fn braced_variant_sequence_composes_header_retries_and_body_occurrences() {
    use SyntaxKind::{
        Comma, EnumKw, EnumVariant, Error, ErrorKw, FromKw, Identifier, LBrace, LParen, Missing,
        RBrace, RParen, Root, TypeExpression, Whitespace,
    };

    // Two owners × two header slots × seven sequence classes × two closes.
    for (keyword, keyword_kind, declaration) in [
        ("enum", EnumKw, SyntaxKind::EnumDeclaration),
        ("error", ErrorKw, SyntaxKind::ErrorDeclaration),
    ] {
        for (header, header_children, error_offset) in [
            (
                " @ 名 ",
                vec![
                    (Whitespace, 1),
                    (Error, 1),
                    (Whitespace, 1),
                    (Identifier, 3),
                    (Whitespace, 1),
                ],
                1,
            ),
            (
                " 名 @ ",
                vec![
                    (Whitespace, 1),
                    (Identifier, 3),
                    (Whitespace, 1),
                    (Error, 1),
                    (Whitespace, 1),
                ],
                5,
            ),
        ] {
            for closed in [true, false] {
                for (body, sequence, variants) in [
                    ("@", vec![(EnumVariant, 1)], vec![vec![(Error, 1)]]),
                    (
                        "@ A",
                        vec![(EnumVariant, 3)],
                        vec![vec![(Error, 1), (Whitespace, 1), (Identifier, 1)]],
                    ),
                    (
                        "A()B",
                        vec![(EnumVariant, 3), (Missing, 0), (EnumVariant, 1)],
                        vec![
                            vec![(Identifier, 1), (LParen, 1), (RParen, 1)],
                            vec![(Identifier, 1)],
                        ],
                    ),
                    (
                        "A,",
                        vec![(EnumVariant, 1), (Comma, 1)],
                        vec![vec![(Identifier, 1)]],
                    ),
                    ("", vec![], vec![]),
                    (
                        "A from @ T",
                        vec![(EnumVariant, 10)],
                        vec![vec![
                            (Identifier, 1),
                            (Whitespace, 1),
                            (FromKw, 4),
                            (Whitespace, 1),
                            (Error, 1),
                            (TypeExpression, 2),
                        ]],
                    ),
                    (
                        "A from",
                        vec![(EnumVariant, 6)],
                        vec![vec![
                            (Identifier, 1),
                            (Whitespace, 1),
                            (FromKw, 4),
                            (TypeExpression, 0),
                        ]],
                    ),
                ] {
                    let source =
                        format!("{keyword}{header}{{{body}{}", if closed { "}" } else { "" });
                    let shell = variant_schema_shell(&source, declaration);
                    let root = shell.parent().unwrap();
                    assert_eq!(root.kind(), Root);
                    assert!(root.parent().is_none());
                    assert_eq!(root.children_with_tokens().count(), 1);
                    assert_eq!(root.to_string(), source);
                    assert_eq!(root.text_range(), shell.text_range());
                    assert_eq!(shell.to_string(), source);
                    let mut expected = vec![(keyword_kind, keyword.len())];
                    expected.extend_from_slice(&header_children);
                    expected.push((LBrace, 1));
                    expected.extend_from_slice(&sequence);
                    expected.push(if closed { (RBrace, 1) } else { (Missing, 0) });
                    assert_variant_sequence_children(&shell, 0, &expected, &source);

                    let start = keyword.len() + header.len() + 1;
                    let actual_variants = shell
                        .children()
                        .filter(|node| node.kind() == EnumVariant)
                        .collect::<Vec<_>>();
                    assert_eq!(actual_variants.len(), variants.len());
                    for (variant, expected) in actual_variants.iter().zip(&variants) {
                        assert_variant_sequence_children(
                            variant,
                            usize::from(variant.text_range().start()),
                            expected,
                            &source,
                        );
                    }
                    if body.starts_with("A from") {
                        let required_type = actual_variants[0].children().next().unwrap();
                        let (offset, children) = if body == "A from" {
                            (6, vec![(Missing, 0)])
                        } else {
                            (8, vec![(Whitespace, 1), (Identifier, 1)])
                        };
                        assert_variant_sequence_children(
                            &required_type,
                            start + offset,
                            &children,
                            &source,
                        );
                    }

                    let header_error = keyword.len() + error_offset;
                    let mut occurrences =
                        vec![(Error, declaration, header_error..header_error + 1)];
                    match body {
                        "@" | "@ A" => occurrences.push((Error, EnumVariant, start..start + 1)),
                        "A()B" => occurrences.push((Missing, declaration, start + 3..start + 3)),
                        "A from @ T" => {
                            occurrences.push((Error, EnumVariant, start + 7..start + 8))
                        }
                        "A from" => {
                            occurrences.push((Missing, TypeExpression, start + 6..start + 6))
                        }
                        _ => {}
                    }
                    if !closed {
                        occurrences.push((Missing, declaration, source.len()..source.len()));
                    }
                    let actual = shell
                        .descendants_with_tokens()
                        .filter(|child| matches!(child.kind(), Error | Missing))
                        .map(|child| {
                            (
                                child.kind(),
                                child.parent().unwrap().kind(),
                                usize::from(child.text_range().start())
                                    ..usize::from(child.text_range().end()),
                            )
                        })
                        .collect::<Vec<_>>();
                    assert_eq!(actual, occurrences, "{source:?}");
                }
            }
        }
    }
}

#[test]
fn braced_variant_sequence_composes_core_slots_and_outer_close() {
    use SyntaxKind::{Comma, EnumVariant, Error, Identifier, LParen, Missing, RParen, Whitespace};

    for (keyword, declaration) in [
        ("enum", SyntaxKind::EnumDeclaration),
        ("error", SyntaxKind::ErrorDeclaration),
    ] {
        for closed in [true, false] {
            for (body, sequence, variants) in [
                ("@", vec![(EnumVariant, 1)], vec![vec![(Error, 1)]]),
                (
                    "@ A",
                    vec![(EnumVariant, 3)],
                    vec![vec![(Error, 1), (Whitespace, 1), (Identifier, 1)]],
                ),
                (
                    "A()B",
                    vec![(EnumVariant, 3), (Missing, 0), (EnumVariant, 1)],
                    vec![
                        vec![(Identifier, 1), (LParen, 1), (RParen, 1)],
                        vec![(Identifier, 1)],
                    ],
                ),
                (
                    "A,",
                    vec![(EnumVariant, 1), (Comma, 1)],
                    vec![vec![(Identifier, 1)]],
                ),
                ("", vec![], vec![]),
            ] {
                let source = format!("{keyword} E{{{body}{}", if closed { "}" } else { "" });
                let shell = braced_variant_sequence_shell(&source, declaration, &sequence, closed);
                let actual_variants = shell
                    .children()
                    .filter(|node| node.kind() == EnumVariant)
                    .collect::<Vec<_>>();
                assert_eq!(actual_variants.len(), variants.len());
                for (variant, expected) in actual_variants.iter().zip(&variants) {
                    assert_variant_sequence_children(
                        variant,
                        usize::from(variant.text_range().start()),
                        expected,
                        &source,
                    );
                }
                let missing = shell
                    .descendants()
                    .filter(|node| node.kind() == Missing)
                    .collect::<Vec<_>>();
                assert_eq!(
                    missing.len(),
                    usize::from(body == "A()B") + usize::from(!closed)
                );
                for node in &missing {
                    assert_eq!(node.parent().as_ref(), Some(&shell));
                }
            }
        }
    }
}

#[test]
fn braced_variant_sequence_composes_from_type_primary_retry_and_outer_close() {
    use SyntaxKind::{EnumVariant, Error, FromKw, Identifier, Missing, TypeExpression, Whitespace};

    for (keyword, declaration) in [
        ("enum", SyntaxKind::EnumDeclaration),
        ("error", SyntaxKind::ErrorDeclaration),
    ] {
        for closed in [true, false] {
            let source = format!("{keyword} E{{A from @ T{}", if closed { "}" } else { "" });
            let shell =
                braced_variant_sequence_shell(&source, declaration, &[(EnumVariant, 10)], closed);
            let variant = shell.children().next().unwrap();
            let start = keyword.len() + 3;
            // FromKw followed by raw Error and an admitted TypeExpression selects
            // Type(Primary); the caller's FromType role applies only to absence.
            assert_variant_sequence_children(
                &variant,
                start,
                &[
                    (Identifier, 1),
                    (Whitespace, 1),
                    (FromKw, 4),
                    (Whitespace, 1),
                    (Error, 1),
                    (TypeExpression, 2),
                ],
                &source,
            );
            let retry = variant.children().next().unwrap();
            assert_variant_sequence_children(
                &retry,
                start + 8,
                &[(Whitespace, 1), (Identifier, 1)],
                &source,
            );
            let missing = shell
                .descendants()
                .filter(|node| node.kind() == Missing)
                .collect::<Vec<_>>();
            assert_eq!(missing.len(), usize::from(!closed));
            if !closed {
                assert_eq!(missing[0].parent().as_ref(), Some(&shell));
            }
        }
    }
}

#[test]
fn braced_variant_sequence_orders_from_type_missing_before_outer_close_missing() {
    use SyntaxKind::{EnumVariant, FromKw, Identifier, Missing, TypeExpression, Whitespace};

    for (keyword, declaration) in [
        ("enum", SyntaxKind::EnumDeclaration),
        ("error", SyntaxKind::ErrorDeclaration),
    ] {
        let source = format!("{keyword} E{{A from");
        let shell = braced_variant_sequence_shell(&source, declaration, &[(EnumVariant, 6)], false);
        let variant = shell.children().next().unwrap();
        assert_variant_sequence_children(
            &variant,
            keyword.len() + 3,
            &[
                (Identifier, 1),
                (Whitespace, 1),
                (FromKw, 4),
                (TypeExpression, 0),
            ],
            &source,
        );
        let required_type = variant.children().next().unwrap();
        assert_variant_sequence_children(&required_type, source.len(), &[(Missing, 0)], &source);
        let missing = shell
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect::<Vec<_>>();
        assert_eq!(missing.len(), 2);
        assert_eq!(missing[0].parent().as_ref(), Some(&required_type));
        assert_eq!(missing[1].parent().as_ref(), Some(&shell));
        assert_eq!(missing[0].text_range(), missing[1].text_range());
    }
}

#[test]
fn braced_variant_sequence_keeps_native_close_after_from_type_missing() {
    use SyntaxKind::{EnumVariant, FromKw, Identifier, Missing, TypeExpression, Whitespace};

    for (keyword, declaration) in [
        ("enum", SyntaxKind::EnumDeclaration),
        ("error", SyntaxKind::ErrorDeclaration),
    ] {
        let source = format!("{keyword} E{{A from}}");
        let shell = braced_variant_sequence_shell(&source, declaration, &[(EnumVariant, 6)], true);
        let root = shell.parent().unwrap();
        assert_eq!(root.text_range(), shell.text_range());
        let variant = shell.children().next().unwrap();
        assert_variant_sequence_children(
            &variant,
            keyword.len() + 3,
            &[
                (Identifier, 1),
                (Whitespace, 1),
                (FromKw, 4),
                (TypeExpression, 0),
            ],
            &source,
        );
        let required_type = variant.children().next().unwrap();
        assert_variant_sequence_children(
            &required_type,
            source.len() - 1,
            &[(Missing, 0)],
            &source,
        );
        let missing = shell
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect::<Vec<_>>();
        assert_eq!(missing.len(), 1);
        assert_eq!(missing[0].parent().as_ref(), Some(&required_type));
        assert_eq!(required_type.parent().as_ref(), Some(&variant));
    }
}

fn braced_variant_sequence_shell(
    source: &str,
    declaration: SyntaxKind,
    sequence: &[(SyntaxKind, usize)],
    closed: bool,
) -> SyntaxNode {
    use SyntaxKind::{EnumKw, ErrorKw, Identifier, LBrace, Missing, RBrace, Root, Whitespace};
    let shell = variant_schema_shell(source, declaration);
    let root = shell.parent().unwrap();
    assert_eq!(root.kind(), Root);
    assert!(root.parent().is_none());
    assert_eq!(root.children_with_tokens().count(), 1);
    assert_eq!(root.to_string(), source);
    assert_eq!(shell.to_string(), source);
    let (keyword, width) = if declaration == SyntaxKind::EnumDeclaration {
        (EnumKw, 4)
    } else {
        (ErrorKw, 5)
    };
    let mut expected = vec![
        (keyword, width),
        (Whitespace, 1),
        (Identifier, 1),
        (LBrace, 1),
    ];
    expected.extend_from_slice(sequence);
    expected.push(if closed { (RBrace, 1) } else { (Missing, 0) });
    assert_variant_sequence_children(&shell, 0, &expected, source);
    shell
}

fn assert_variant_sequence_children(
    owner: &SyntaxNode,
    start: usize,
    expected: &[(SyntaxKind, usize)],
    source: &str,
) {
    use SyntaxKind::{EnumVariant, Missing, TypeExpression};
    let children = owner.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children.len(), expected.len(), "{source:?}");
    let mut at = start;
    for (child, &(kind, width)) in children.iter().zip(expected) {
        assert_eq!(child.kind(), kind, "{source:?}");
        assert_eq!(child.parent().as_ref(), Some(owner));
        assert_eq!(
            child.as_node().is_some(),
            matches!(kind, EnumVariant | Missing | TypeExpression)
        );
        assert_eq!(
            usize::from(child.text_range().start())..usize::from(child.text_range().end()),
            at..at + width
        );
        if kind == Missing {
            assert_eq!(width, 0);
            assert!(
                child
                    .as_node()
                    .unwrap()
                    .children_with_tokens()
                    .next()
                    .is_none()
            );
        } else if kind != SyntaxKind::Error && child.as_token().is_some() {
            assert_eq!(child.to_string(), source[at..at + width]);
        }
        at += width;
    }
    assert_eq!(
        usize::from(owner.text_range().start())..usize::from(owner.text_range().end()),
        start..at
    );
}

#[test]
fn enum_error_delimited_field_sequence_composes_ordered_occurrences() {
    for (prefix, declaration) in [
        ("enum E{A{", SyntaxKind::EnumDeclaration),
        ("error E{A{", SyntaxKind::ErrorDeclaration),
        ("enum E{A(", SyntaxKind::EnumDeclaration),
        ("error E{A(", SyntaxKind::ErrorDeclaration),
    ] {
        super::struct_decl::assert_delimited_field_sequence_composition(prefix, "}}", declaration);
    }
}

#[test]
fn enum_error_tuple_field_sequence_matching_close_has_direct_owners() {
    use SyntaxKind::{Comma, LParen, RBrace, RParen, StructField};
    for (source, declaration, start) in [
        ("enum E{A(T U,=V)}", SyntaxKind::EnumDeclaration, 9),
        ("error E{A(T U,=V)}", SyntaxKind::ErrorDeclaration, 10),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = syntax_root(green);
        let variant = super::struct_decl::assert_matching_tuple_composition(
            &root,
            start,
            declaration,
            source,
        );
        super::struct_decl::assert_sequence_composition_children(
            &variant,
            start - 1,
            &[
                (LParen, 1),
                (StructField, 3),
                (Comma, 1),
                (StructField, 2),
                (RParen, 1),
            ],
            source,
        );
        let owner = variant.parent().unwrap();
        assert_eq!(owner.kind(), declaration);
        super::struct_decl::assert_sequence_composition_children(
            &owner,
            start + 7,
            &[(RBrace, 1)],
            source,
        );
        assert_eq!(
            variant.next_sibling_or_token(),
            owner.children_with_tokens().last()
        );
    }
}

#[test]
fn enum_error_delimited_field_sequence_borrows_foreign_close_after_separator_error() {
    use SyntaxKind::{Error, LBrace, LParen, Missing, StructField};
    for (keyword, declaration) in [
        ("enum", SyntaxKind::EnumDeclaration),
        ("error", SyntaxKind::ErrorDeclaration),
    ] {
        for (payload, open, field_len) in [("{x:T;", LBrace, 3), ("(T U;", LParen, 3)] {
            let accepted = format!("{keyword} E=A{payload}");
            let source = format!("{accepted} ]");
            let (green, exit, remainder) =
                run_statement_normalized(&source, 0, LineEntry::InLine, None);
            assert_eq!(green.to_string(), accepted);
            assert_eq!(remainder, "");
            let NormalizedExit::Complete(Err(Either::Left(mut item)), _) = exit else {
                panic!("foreign close must stay pending");
            };
            assert_eq!(item.payload_view().token_kind(), Some(TokenKind::RBracket));
            assert_eq!(emit_pending_leading_text(&mut item), " ");
            let root = syntax_root(green);
            let variant = root
                .descendants()
                .find(|n| n.kind() == SyntaxKind::EnumVariant)
                .unwrap();
            let start = accepted.len() - payload.len();
            let field = variant
                .children()
                .find(|n| n.kind() == StructField)
                .unwrap();
            super::struct_decl::assert_composition_field_ancestry(&field, declaration);
            super::struct_decl::assert_sequence_composition_children(
                &variant,
                start,
                &[
                    (open, 1),
                    (StructField, field_len),
                    (Error, 1),
                    (Missing, 0),
                ],
                &source,
            );
            let missing = root
                .descendants()
                .filter(|n| n.kind() == Missing)
                .collect::<Vec<_>>();
            assert_eq!(missing.len(), 1);
            assert_eq!(missing[0].parent().as_ref(), Some(&variant));
            assert!(!root.descendants().any(|n| matches!(
                n.kind(),
                SyntaxKind::StructFieldForeignClose | SyntaxKind::Invalid
            )));
        }
    }
}

#[test]
fn enum_error_empty_field_list_close_missing_has_direct_cst_slot() {
    for (prefix, suffix, declaration) in [
        ("enum E{A{", "}}", SyntaxKind::EnumDeclaration),
        ("enum E{A(", ")}", SyntaxKind::EnumDeclaration),
        ("error E{A{", "}}", SyntaxKind::ErrorDeclaration),
        ("error E{A(", ")}", SyntaxKind::ErrorDeclaration),
    ] {
        super::struct_decl::assert_empty_field_list_close_missing_cst(
            prefix,
            suffix,
            &[SyntaxKind::EnumVariant, declaration],
        );
    }
}

#[test]
fn enum_error_field_separators_have_direct_cst_slots() {
    for (prefix, suffix, declaration) in [
        ("enum E{A{", "}}", SyntaxKind::EnumDeclaration),
        ("enum E{A(", ")}", SyntaxKind::EnumDeclaration),
        ("error E{A{", "}}", SyntaxKind::ErrorDeclaration),
        ("error E{A(", ")}", SyntaxKind::ErrorDeclaration),
    ] {
        super::struct_decl::assert_field_separators_cst(
            prefix,
            suffix,
            &[SyntaxKind::EnumVariant, declaration],
        );
    }
}

#[test]
fn enum_error_fresh_tuple_field_items_have_direct_cst_slots() {
    for (prefix, declaration) in [
        ("enum E{A(", SyntaxKind::EnumDeclaration),
        ("error E{A(", SyntaxKind::ErrorDeclaration),
    ] {
        super::struct_decl::assert_fresh_tuple_field_items_cst(
            prefix,
            ")}",
            &[SyntaxKind::EnumVariant, declaration],
        );
    }
}

#[test]
fn enum_error_fresh_named_field_items_have_direct_cst_slots() {
    for (prefix, declaration) in [
        ("enum E{A{", SyntaxKind::EnumDeclaration),
        ("error E{A{", SyntaxKind::ErrorDeclaration),
    ] {
        super::struct_decl::assert_fresh_named_field_items_cst(
            prefix,
            "}}",
            &[SyntaxKind::EnumVariant, declaration],
        );
    }
}

#[test]
fn enum_error_named_field_head_has_direct_cst_slots_and_type_retry() {
    for (prefix, declaration) in [
        ("enum E{A{", SyntaxKind::EnumDeclaration),
        ("error E{A{", SyntaxKind::ErrorDeclaration),
    ] {
        super::struct_decl::assert_named_field_head_cst(
            prefix,
            "}}",
            &[SyntaxKind::EnumVariant, declaration],
        );
    }
}

use crate::{
    handoff::Either,
    lexical::{
        item::{BorrowedTarget, Boundary},
        yumark::{FenceOpener, FencePrefixPolicy},
    },
};

fn syntax_root(green: GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green)
}

fn count(root: &SyntaxNode, kind: SyntaxKind) -> usize {
    if kind == SyntaxKind::Error {
        return crate::tests::recovery_output::recovery_groups(root).len();
    }
    root.descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

fn identifier_texts(node: &SyntaxNode) -> Vec<String> {
    node.descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::Identifier)
        .map(|token| token.text().to_owned())
        .collect()
}

fn variant_schema_shell(source: &str, declaration: SyntaxKind) -> SyntaxNode {
    let (green, _, remainder) = if declaration == SyntaxKind::EnumDeclaration {
        run_enum_declaration(source, 0, 100, LineEntry::InLine, None)
    } else {
        run_error_declaration(source, 0, 100, LineEntry::InLine, None)
    };
    assert_eq!(remainder, "");
    let root = syntax_root(green);
    assert!(
        !root
            .descendants_with_tokens()
            .any(|child| child.kind() == SyntaxKind::Invalid)
    );
    let shells = root.children().collect::<Vec<_>>();
    assert_eq!(shells.len(), 1);
    assert_eq!(shells[0].kind(), declaration);
    assert_eq!(shells[0].parent().as_ref(), Some(&root));
    shells[0].clone()
}

#[test]
fn declaration_variant_item_absence_and_terminal_error_have_direct_cst_slots() {
    use SyntaxKind::{EnumVariant, Error, Missing};

    for (keyword, declaration) in [
        ("enum", SyntaxKind::EnumDeclaration),
        ("error", SyntaxKind::ErrorDeclaration),
    ] {
        for (suffix, expected, width) in [(" E =", Missing, 0), (" E = @", Error, 1)] {
            let source = format!("{keyword}{suffix}");
            let shell = variant_schema_shell(&source, declaration);
            let variants = shell.children().collect::<Vec<_>>();
            assert_eq!(variants.len(), 1);
            let variant = &variants[0];
            assert_eq!(variant.kind(), EnumVariant);
            assert_eq!(variant.parent().as_ref(), Some(&shell));
            // Initial leading is native trivia owned by the Variant.
            let children = variant
                .children_with_tokens()
                .skip_while(|child| {
                    matches!(child.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline)
                })
                .collect::<Vec<_>>();
            assert_eq!(children.len(), 1);
            assert_eq!(children[0].kind(), expected);
            assert_eq!(children[0].as_token().is_some(), expected == Error);
            assert_eq!(children[0].parent().as_ref(), Some(variant));
            assert_eq!(
                usize::from(children[0].text_range().start()),
                source.len() - width
            );
            assert_eq!(usize::from(children[0].text_range().end()), source.len());
            // A terminal Error has no admitted name or second Item Missing.
            assert!(!shell.children().any(|node| node.kind() == Missing));
        }
    }
}

#[test]
fn declaration_variant_name_retry_has_direct_cst_slots_in_all_forms() {
    use SyntaxKind::{EnumVariant, Error, Identifier, Missing, Whitespace};

    for (keyword, declaration) in [
        ("enum", SyntaxKind::EnumDeclaration),
        ("error", SyntaxKind::ErrorDeclaration),
    ] {
        for (prefix, suffix) in [
            (" E {", "}"),
            (" E = ", ""),
            (" E:\n  ", ""),
            (" E =\n  ", ""),
        ] {
            let source = format!("{keyword}{prefix}@ A{suffix}");
            let shell = variant_schema_shell(&source, declaration);
            let variants = shell.children().collect::<Vec<_>>();
            assert_eq!(variants.len(), 1);
            let variant = &variants[0];
            assert_eq!(variant.kind(), EnumVariant);
            assert_eq!(variant.parent().as_ref(), Some(&shell));
            // Initial leading precedes the recovery slot; retry leading follows Error.
            let children = variant
                .children_with_tokens()
                .skip_while(|child| {
                    matches!(child.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline)
                })
                .collect::<Vec<_>>();
            assert_eq!(
                children
                    .iter()
                    .map(|child| child.kind())
                    .collect::<Vec<_>>(),
                [Error, Whitespace, Identifier]
            );
            let start = keyword.len() + prefix.len();
            for (offset, child) in children.iter().enumerate() {
                assert!(child.as_token().is_some());
                assert_eq!(child.parent().as_ref(), Some(variant));
                assert_eq!(usize::from(child.text_range().start()), start + offset);
                assert_eq!(usize::from(child.text_range().end()), start + offset + 1);
            }
            // The immediate native-trivia/name continuation selects Name, not Item.
            assert!(!shell.descendants().any(|node| node.kind() == Missing));
        }
    }
}

#[test]
fn declaration_variant_separator_and_required_item_have_distinct_direct_cst_parents() {
    use SyntaxKind::{Comma, EnumVariant, Missing};

    for (keyword, declaration) in [
        ("enum", SyntaxKind::EnumDeclaration),
        ("error", SyntaxKind::ErrorDeclaration),
    ] {
        for (suffix, required_item, offset) in [(" E {A()B}", false, 7), (" E {A,,B}", true, 6)] {
            let source = format!("{keyword}{suffix}");
            let shell = variant_schema_shell(&source, declaration);
            let nodes = shell.children().collect::<Vec<_>>();
            assert_eq!(nodes.len(), 3);
            assert_eq!(nodes[0].kind(), EnumVariant);
            assert_eq!(nodes[2].kind(), EnumVariant);
            let missing = if required_item {
                assert_eq!(nodes[1].kind(), EnumVariant);
                let children = nodes[1].children_with_tokens().collect::<Vec<_>>();
                assert_eq!(children.len(), 1);
                assert_eq!(children[0].kind(), Missing);
                assert_eq!(children[0].parent().as_ref(), Some(&nodes[1]));
                assert_eq!(nodes[1].next_sibling_or_token().unwrap().kind(), Comma);
                children[0].as_node().unwrap().clone()
            } else {
                assert_eq!(nodes[1].kind(), Missing);
                assert_eq!(
                    nodes[1].prev_sibling_or_token().unwrap().as_node(),
                    Some(&nodes[0])
                );
                assert_eq!(
                    nodes[1].next_sibling_or_token().unwrap().as_node(),
                    Some(&nodes[2])
                );
                nodes[1].clone()
            };
            for node in &nodes {
                assert_eq!(node.parent().as_ref(), Some(&shell));
            }
            assert!(missing.text_range().is_empty());
            assert_eq!(
                usize::from(missing.text_range().start()),
                keyword.len() + offset
            );
        }
    }
}

#[test]
fn declaration_variant_from_type_primary_retry_has_direct_enum_error_cst_evidence() {
    use SyntaxKind::{
        EnumVariant, Error, FromKw, Identifier, Invalid, Missing, TypeExpression, Whitespace,
    };

    for (source, declaration, error_start) in [
        ("enum E = A from @ T", SyntaxKind::EnumDeclaration, 16),
        ("error E = A from @ T", SyntaxKind::ErrorDeclaration, 17),
    ] {
        let (green, _, remainder) = if declaration == SyntaxKind::EnumDeclaration {
            run_enum_declaration(source, 0, 100, LineEntry::InLine, None)
        } else {
            run_error_declaration(source, 0, 100, LineEntry::InLine, None)
        };
        assert_eq!(green.to_string(), source);
        assert_eq!(remainder, "");
        let root = syntax_root(green);
        let shells = root.children().collect::<Vec<_>>();
        assert_eq!(shells.len(), 1);
        let shell = &shells[0];
        assert_eq!(shell.kind(), declaration);
        assert_eq!(shell.parent().as_ref(), Some(&root));
        let variants = shell
            .children()
            .filter(|node| node.kind() == EnumVariant)
            .collect::<Vec<_>>();
        assert_eq!(variants.len(), 1);
        let variant = &variants[0];
        assert_eq!(variant.parent().as_ref(), Some(shell));
        let children = variant.children_with_tokens().collect::<Vec<_>>();
        // FromKw and the admitted TypeExpression retry select Type::Primary
        // within the full declaration shell, independently of Error spelling.
        assert_eq!(
            children
                .iter()
                .map(|child| (child.kind(), child.as_token().is_some()))
                .collect::<Vec<_>>(),
            [
                (Whitespace, true),
                (Identifier, true),
                (Whitespace, true),
                (FromKw, true),
                (Whitespace, true),
                (Error, true),
                (TypeExpression, false),
            ]
        );
        let error = children[5].as_token().unwrap();
        assert_eq!(error.parent().as_ref(), Some(variant));
        let range = usize::from(error.text_range().start())..usize::from(error.text_range().end());
        assert_eq!(range, error_start..error_start + 1);
        assert_eq!(error.text(), &source[range]);
        let retry = children[6].as_node().unwrap();
        assert_eq!(retry.parent().as_ref(), Some(variant));
        assert_eq!(
            usize::from(retry.text_range().start())..usize::from(retry.text_range().end()),
            error_start + 1..error_start + 3
        );
        // The retry owns its leading as native whitespace outside the Error.
        assert_eq!(
            retry
                .children_with_tokens()
                .map(|child| (child.kind(), child.as_token().is_some(), child.to_string()))
                .collect::<Vec<_>>(),
            [
                (Whitespace, true, " ".to_owned()),
                (Identifier, true, "T".to_owned()),
            ]
        );
        assert!(
            !root
                .descendants_with_tokens()
                .any(|child| matches!(child.kind(), Missing | Invalid))
        );
    }
}

#[test]
fn declaration_variant_from_type_terminal_primary_has_direct_enum_error_cst_evidence() {
    use SyntaxKind::{
        EnumVariant, Error, FromKw, Identifier, Invalid, Missing, TypeExpression, Whitespace,
    };

    for (source, declaration) in [
        ("enum E = A from@", SyntaxKind::EnumDeclaration),
        ("error E = A from@", SyntaxKind::ErrorDeclaration),
    ] {
        let (green, _, remainder) = if declaration == SyntaxKind::EnumDeclaration {
            run_enum_declaration(source, 0, 100, LineEntry::InLine, None)
        } else {
            run_error_declaration(source, 0, 100, LineEntry::InLine, None)
        };
        assert_eq!(green.to_string(), source);
        assert_eq!(remainder, "");
        let root = syntax_root(green);
        let shells = root.children().collect::<Vec<_>>();
        assert_eq!(shells.len(), 1);
        let shell = &shells[0];
        assert_eq!(shell.kind(), declaration);
        assert_eq!(shell.parent().as_ref(), Some(&root));
        let variants = shell
            .children()
            .filter(|node| node.kind() == EnumVariant)
            .collect::<Vec<_>>();
        assert_eq!(variants.len(), 1);
        let variant = &variants[0];
        assert_eq!(variant.parent().as_ref(), Some(shell));
        let children = variant.children_with_tokens().collect::<Vec<_>>();
        // The full declaration shell and direct FromKw select the required
        // FromType slot; its nonempty malformed primary remains Type::Primary.
        // Error spelling is source-conservation evidence, not classification.
        assert_eq!(
            children
                .iter()
                .map(|child| (child.kind(), child.as_token().is_some()))
                .collect::<Vec<_>>(),
            [
                (Whitespace, true),
                (Identifier, true),
                (Whitespace, true),
                (FromKw, true),
                (Error, true),
            ]
        );
        // FromKw and EOF bound the sole maximal direct Error group.
        let error = children[4].as_token().unwrap();
        assert_eq!(error.parent().as_ref(), Some(variant));
        let range = usize::from(error.text_range().start())..usize::from(error.text_range().end());
        assert_eq!(range, source.len() - 1..source.len());
        assert_eq!(error.text(), &source[range]);
        assert!(
            !root
                .descendants_with_tokens()
                .any(|child| matches!(child.kind(), TypeExpression | Missing | Invalid))
        );
    }
}

#[test]
fn declaration_variant_from_type_missing_has_direct_enum_error_cst_evidence() {
    use SyntaxKind::{
        EnumVariant, Error, FromKw, Identifier, Invalid, Missing, TypeExpression, Whitespace,
    };

    for (keyword, declaration) in [
        ("enum", SyntaxKind::EnumDeclaration),
        ("error", SyntaxKind::ErrorDeclaration),
    ] {
        for active_stop in [false, true] {
            let prefix = format!("{keyword} E = A from");
            let source = if active_stop {
                format!("{prefix} /*pending*/ : tail")
            } else {
                prefix.clone()
            };
            let stops = if active_stop { STOP_COLON } else { 0 };
            let (green, exit, remainder) = if keyword == "enum" {
                run_enum_declaration(&source, stops, 100, LineEntry::InLine, None)
            } else {
                run_error_declaration(&source, stops, 100, LineEntry::InLine, None)
            };
            assert_eq!(green.to_string(), prefix, "{source:?}");
            if active_stop {
                let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), _)) = exit else {
                    panic!("active Colon must remain pending: {source:?}");
                };
                assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Colon));
                assert_eq!(emit_pending_leading_text(&mut item), " /*pending*/ ");
                assert_eq!(remainder, " tail");
            } else {
                assert_eq!(remainder, "");
            }

            let root = syntax_root(green);
            let shell = root
                .children()
                .find(|node| node.kind() == declaration)
                .unwrap();
            assert_eq!(shell.parent(), Some(root.clone()));
            let variants = shell
                .children()
                .filter(|node| node.kind() == EnumVariant)
                .collect::<Vec<_>>();
            assert_eq!(variants.len(), 1, "{source:?}");
            let variant = &variants[0];
            assert_eq!(variant.parent().as_ref(), Some(&shell));
            let at = prefix.len();
            assert_eq!(
                variant
                    .children_with_tokens()
                    .map(|child| (
                        child.kind(),
                        child.as_node().is_some(),
                        usize::from(child.text_range().start())
                            ..usize::from(child.text_range().end()),
                        child.to_string(),
                    ))
                    .collect::<Vec<_>>(),
                [
                    (
                        Whitespace,
                        false,
                        at - " A from".len()..at - "A from".len(),
                        " ".to_owned(),
                    ),
                    (Identifier, false, at - 6..at - 5, "A".to_owned()),
                    (Whitespace, false, at - 5..at - 4, " ".to_owned()),
                    (FromKw, false, at - 4..at, "from".to_owned()),
                    (TypeExpression, true, at..at, String::new()),
                ],
                "{source:?}",
            );
            let payload = variant.children().next().unwrap();
            let children = payload.children_with_tokens().collect::<Vec<_>>();
            assert_eq!(children.len(), 1);
            let missing = children[0].as_node().unwrap();
            assert_eq!(missing.kind(), Missing);
            assert_eq!(missing.parent(), Some(payload.clone()));
            assert_eq!(usize::from(missing.text_range().start()), at);
            assert!(missing.text_range().is_empty());
            assert_eq!(missing.children_with_tokens().count(), 0);
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
    }
}

#[test]
fn declaration_variant_core_slots_have_direct_enum_error_cst_evidence() {
    use SyntaxKind::{EnumVariant, Error, Identifier, Missing, Whitespace};
    // Publication and handoff selects Name only on an admitted raw-name retry.
    // The enclosing declaration supplies the Enum/Error distinction; records
    // in the isolated typed harness remain compatibility evidence only.
    for (keyword, declaration) in [
        ("enum", SyntaxKind::EnumDeclaration),
        ("error", SyntaxKind::ErrorDeclaration),
    ] {
        for (body, name_retry) in [
            ("{  @ $ 名}", true),
            ("=  @ $ 名", true),
            (":\r\n  @ $ 名", true),
            ("=\r\n  @ $ 名", true),
            ("{  @ $}", false),
            ("=  @ $", false),
            (":\r\n  @ $", false),
            ("=\r\n  @ $", false),
        ] {
            let source = format!("{keyword} E{body}");
            let (green, _) = run_statement(&source);
            assert_eq!(green.to_string(), source);
            let root = syntax_root(green);
            let shell = root
                .descendants()
                .find(|node| node.kind() == declaration)
                .unwrap();
            let variants = shell
                .children()
                .filter(|node| node.kind() == EnumVariant)
                .collect::<Vec<_>>();
            assert_eq!(variants.len(), 1, "{source:?}");
            let variant = &variants[0];
            assert_eq!(variant.parent().as_ref(), Some(&shell));
            let children = variant.children_with_tokens().collect::<Vec<_>>();
            let first_error = children
                .iter()
                .position(|child| child.kind() == Error)
                .unwrap();
            let errors = &children[first_error..first_error + 3];
            assert_eq!(
                errors
                    .iter()
                    .map(|child| (child.kind(), child.to_string()))
                    .collect::<Vec<_>>(),
                [
                    (Error, "@".to_owned()),
                    (Error, " ".to_owned()),
                    (Error, "$".to_owned())
                ]
            );
            for error in errors {
                assert!(error.as_token().is_some());
                assert_eq!(error.parent().as_ref(), Some(variant));
            }
            let start = source.find('@').unwrap();
            assert_eq!(usize::from(errors[0].text_range().start()), start);
            assert_eq!(usize::from(errors[2].text_range().end()), start + 3);
            assert!(
                children[..first_error]
                    .iter()
                    .all(|child| matches!(child.kind(), Whitespace | SyntaxKind::Newline))
            );
            assert_eq!(children[first_error - 1].kind(), Whitespace);
            assert_eq!(children[first_error - 1].to_string(), "  ");
            let tail = children[first_error + 3..]
                .iter()
                .map(|child| (child.kind(), child.to_string()))
                .collect::<Vec<_>>();
            assert_eq!(
                tail,
                if name_retry {
                    vec![(Whitespace, " ".to_owned()), (Identifier, "名".to_owned())]
                } else {
                    vec![]
                },
                "{source:?}"
            );
            assert!(variant.children().all(|node| node.kind() != Missing));
        }
        for body in ["=", "=  ", "=\r\n", "{,A}"] {
            let source = format!("{keyword} E{body}");
            let (green, _) = run_statement(&source);
            assert_eq!(green.to_string(), source);
            let root = syntax_root(green);
            let shell = root
                .descendants()
                .find(|node| node.kind() == declaration)
                .unwrap();
            let variant = shell
                .children()
                .find(|node| node.kind() == EnumVariant)
                .unwrap();
            let children = variant.children_with_tokens().collect::<Vec<_>>();
            assert_eq!(children.len(), 1, "{source:?}");
            let missing = children[0].as_node().unwrap();
            assert_eq!(missing.kind(), Missing);
            assert_eq!(missing.parent().as_ref(), Some(&variant));
            assert!(missing.children_with_tokens().next().is_none());
            let at = source.find(',').unwrap_or(source.len());
            assert_eq!(usize::from(missing.text_range().start()), at);
            assert!(missing.text_range().is_empty());
        }
        // A completed payload prevents B from being admitted as A's Type.
        let source = format!("{keyword} E{{A()B}}");
        let (green, _) = run_statement(&source);
        assert_eq!(green.to_string(), source);
        let root = syntax_root(green);
        let shell = root
            .descendants()
            .find(|node| node.kind() == declaration)
            .unwrap();
        let children = shell.children().collect::<Vec<_>>();
        let first = children
            .iter()
            .position(|node| node.kind() == EnumVariant)
            .unwrap();
        assert_eq!(
            children[first..]
                .iter()
                .map(|node| (node.kind(), node.text().to_string()))
                .collect::<Vec<_>>(),
            [
                (EnumVariant, "A()".to_owned()),
                (Missing, String::new()),
                (EnumVariant, "B".to_owned())
            ]
        );
        let missing = &children[first + 1];
        assert_eq!(missing.parent().as_ref(), Some(&shell));
        assert!(missing.children_with_tokens().next().is_none());
        assert!(missing.text_range().is_empty());
        assert_eq!(
            usize::from(missing.text_range().start()),
            source.find('B').unwrap()
        );
    }
}

fn active_fence() -> FenceBoundary {
    FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    }
}

fn variant_role(owner: VariantOwner, slot: VariantDeclarationRole) -> GrammarRole {
    GrammarRole::Declaration(match owner {
        VariantOwner::Enum => DeclarationRole::Enum(EnumDeclarationRole::Variant(slot)),
        VariantOwner::Error => DeclarationRole::Error(ErrorDeclarationRole::Variant(slot)),
    })
}

fn record(
    role: GrammarRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    id: usize,
) -> CommittedRecoveryRecord {
    let expected = match role {
        GrammarRole::ClosingDelimiter { delimiter, .. } => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter))
        }
        GrammarRole::Declaration(
            DeclarationRole::Enum(EnumDeclarationRole::Variant(VariantDeclarationRole::Separator))
            | DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::Separator,
            )),
        ) => ExpectedSyntax::DelimitedSequenceSeparator,
        GrammarRole::Declaration(
            DeclarationRole::Enum(EnumDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldSeparator,
            ))
            | DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldSeparator,
            )),
        ) => ExpectedSyntax::DelimitedSequenceSeparator,
        _ => ExpectedSyntax::Identifier,
    };
    CommittedRecoveryRecord {
        id: DiagnosticId(id as u32),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected: if kind == RecoveryKind::Error {
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }])
        } else {
            Arc::from([])
        },
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

#[test]
fn typed_variant_field_sequence_uses_the_payload_separator_role() {
    for owner in [VariantOwner::Enum, VariantOwner::Error] {
        for (source, role, kind, range) in [(
            "{V{a:A b:B}}",
            variant_role(owner, VariantDeclarationRole::NamedFieldSeparator),
            RecoveryKind::Missing,
            7..7,
        )] {
            let (green, records, _, _) = typed_variant(
                source,
                owner,
                VariantSequenceForm::Braced,
                false,
                0,
                700,
                None,
                None,
                false,
            );
            assert_eq!(green.to_string(), source, "{owner:?} {source:?}");
            assert_eq!(
                records,
                [record(role, kind, 700 + range.start..700 + range.end, 0)]
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn typed_variant<'a>(
    source: &'a str,
    owner: VariantOwner,
    form: VariantSequenceForm,
    yield_with: bool,
    stops: Stops,
    origin: usize,
    fence: Option<&FenceBoundary>,
    frozen: Option<&[CommittedRecoveryRecord]>,
    seeded: bool,
) -> (
    GreenNode,
    Vec<CommittedRecoveryRecord>,
    Option<NormalizedExit>,
    &'a str,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut builder = frozen.map_or_else(GreenNodeBuilder::new, |records| {
        recover = Recover::reconcile_for_test(recover.operators(), records);
        GreenNodeBuilder::new()
    });
    builder.start_node(SyntaxKind::Root.into());
    if seeded {
        let seed = record(
            variant_role(owner, VariantDeclarationRole::Name),
            RecoveryKind::Missing,
            0..0,
            0,
        );
        builder.start_node(SyntaxKind::Missing.into());
        builder.finish_node();
        recover.commit_recovery_for_test(crate::cursor::recovery::RecoveryDraft::new(
            seed.site,
            seed.kind,
            seed.unexpected,
            seed.expectations,
            0,
        ));
    }
    let exit = declaration_variant_owner_witness(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
        owner,
        form,
        yield_with,
        0,
        stops,
        origin,
        if fence.is_some() {
            LineEntry::PhysicalStart
        } else {
            LineEntry::InLine
        },
        fence,
    );
    builder.finish_node();
    let (green, records) = (builder.finish(), recover.finish_recoveries_for_test());
    (green, records, exit, input)
}

#[test]
fn typed_variant_payload_scoped_caller_stops_preserve_pending_items() {
    use crate::lexical::stops::{
        STOP_ARROW, STOP_COLON, STOP_ELSE, STOP_ELSIF, STOP_LBRACE, STOP_WITH,
    };
    for owner in [VariantOwner::Enum, VariantOwner::Error] {
        for (prefix, stop, stops, recovery) in [
            ("= A", ":", STOP_COLON, None),
            ("= A", "{", STOP_LBRACE, None),
            ("= A", "else", STOP_ELSE, None),
            ("= A", "elsif", STOP_ELSIF, None),
            ("= A", "with", STOP_WITH, None),
            ("= A from", ":", STOP_COLON, Some(RecoveryKind::Missing)),
            ("= A from", "{", STOP_LBRACE, Some(RecoveryKind::Missing)),
            ("= A from @", ":", STOP_COLON, Some(RecoveryKind::Error)),
            ("= A @", ":", STOP_COLON, Some(RecoveryKind::Error)),
            ("= A T", ":", STOP_COLON, None),
            ("= A from T", "else", STOP_ELSE, None),
            ("= A from (T -> U)", "->", STOP_ARROW, None),
            ("= A F(T->U)", "->", STOP_ARROW, None),
        ] {
            let source = format!("{prefix} /*pending*/ {stop} tail");
            let (green, records, exit, remainder) = typed_variant(
                &source,
                owner,
                VariantSequenceForm::EqualsInline,
                false,
                stops,
                0,
                None,
                None,
                false,
            );
            assert_eq!(green.to_string(), prefix, "{source}");
            assert_eq!(remainder, " tail", "{source}");
            assert_eq!(records.len(), usize::from(recovery.is_some()), "{source}");
            if let Some(kind) = recovery {
                assert_eq!(records[0].kind, kind, "{source}");
                if kind == RecoveryKind::Missing {
                    assert_eq!(
                        records[0].site.role,
                        variant_role(owner, VariantDeclarationRole::FromType)
                    );
                    let root = syntax_root(green);
                    let missing = root
                        .descendants()
                        .find(|node| node.kind() == SyntaxKind::Missing)
                        .unwrap();
                    assert_eq!(missing.parent().unwrap().kind(), SyntaxKind::TypeExpression);
                } else {
                    assert!(
                        matches!(records[0].site.role, GrammarRole::Type(_)),
                        "{source}"
                    );
                }
            }
            let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), _)) = exit else {
                panic!("caller boundary pending: {source}")
            };
            assert_eq!(item.payload_view().spelling(), Some(stop), "{source}");
            assert_eq!(
                emit_pending_leading_text(&mut item),
                " /*pending*/ ",
                "{source}"
            );
        }
        for (source, recovery_count, yield_with, stops) in [
            ("= A from T -> with", 0, false, STOP_WITH),
            ("= A from T -> @ with", 1, false, STOP_WITH),
            ("= A from T -> with", 0, true, 0),
            ("= A from T -> @ with", 1, true, 0),
        ] {
            let (green, records, _, remainder) = typed_variant(
                source,
                owner,
                VariantSequenceForm::EqualsInline,
                yield_with,
                stops,
                0,
                None,
                None,
                false,
            );
            assert_eq!(green.to_string(), source, "{owner:?}: {source}");
            assert!(remainder.is_empty(), "{owner:?}: {source}");
            assert_eq!(records.len(), recovery_count, "{owner:?}: {source}");
            if recovery_count != 0 {
                assert_eq!(records[0].kind, RecoveryKind::Error);
                assert_eq!(
                    records[0].site.role,
                    GrammarRole::Type(crate::recovery_record::TypeRole::ArrowRhs)
                );
            }
            let root = syntax_root(green);
            let arrow = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
                .unwrap();
            assert!(arrow.children().any(|node| {
                node.kind() == SyntaxKind::TypeExpression
                    && node.text().to_string().ends_with("with")
            }));
        }
    }
}

#[test]
fn typed_variant_inactive_brace_and_semicolon_preserve_payload_and_progress() {
    for owner in [VariantOwner::Enum, VariantOwner::Error] {
        let (green, records, _, remainder) = typed_variant(
            "= A {x:T}",
            owner,
            VariantSequenceForm::EqualsInline,
            false,
            0,
            0,
            None,
            None,
            false,
        );
        assert_eq!(green.to_string(), "= A {x:T}");
        assert!(records.is_empty());
        assert!(remainder.is_empty());
        assert_eq!(count(&syntax_root(green), SyntaxKind::StructField), 1);
        let (green, records, _, remainder) = typed_variant(
            "= A ;",
            owner,
            VariantSequenceForm::EqualsInline,
            false,
            0,
            0,
            None,
            None,
            false,
        );
        assert_eq!(green.to_string(), "= A ;");
        assert!(remainder.is_empty());
        assert_eq!(records.len(), 2);
        assert_eq!(
            records[0].site.role,
            variant_role(owner, VariantDeclarationRole::Separator)
        );
        assert_eq!(
            records[1].site.role,
            variant_role(owner, VariantDeclarationRole::Item)
        );
        assert_eq!(records[1].kind, RecoveryKind::Error);
    }
}

#[test]
fn typed_variant_child_records_keep_their_role_and_order_without_duplicate_variant_records() {
    for owner in [VariantOwner::Enum, VariantOwner::Error] {
        let source = "= A from (T -> ) | @";
        let (green, records, _, _) = typed_variant(
            source,
            owner,
            VariantSequenceForm::EqualsInline,
            false,
            0,
            700,
            None,
            None,
            false,
        );
        assert_eq!(green.to_string(), source);
        let child_role = GrammarRole::Type(crate::recovery_record::TypeRole::ArrowRhs);
        let close = 700 + source.find(')').unwrap();
        let malformed = 700 + source.find('@').unwrap();
        let mut child = record(child_role, RecoveryKind::Missing, close..close, 0);
        child.expectations = Arc::from([SyntaxExpectation {
            role: child_role,
            expected: ExpectedSyntax::TypeExpression,
            range: close..close,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]);
        let expected = vec![
            child,
            record(
                variant_role(owner, VariantDeclarationRole::Item),
                RecoveryKind::Error,
                malformed..malformed + 1,
                1,
            ),
        ];
        // The variant recovery design's Publication and handoff section keeps
        // nested payload records at their child owner, with no Item cascade.
        assert_eq!(records, expected, "{owner:?}");
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::Missing), 1);
        assert_eq!(count(&root, SyntaxKind::Error), 1);
        let (_, frozen, _, _) = typed_variant(
            source,
            owner,
            VariantSequenceForm::EqualsInline,
            false,
            0,
            700,
            None,
            Some(&expected),
            false,
        );
        assert_eq!(frozen, expected);
    }
}

#[test]
fn typed_variant_named_field_records_keep_each_outer_owner() {
    let source = "{V{@ : T}}";
    let at = 700 + source.find('@').expect("malformed field name");
    for owner in [VariantOwner::Enum, VariantOwner::Error] {
        let (green, records, _, _) = typed_variant(
            source,
            owner,
            VariantSequenceForm::Braced,
            false,
            0,
            700,
            None,
            None,
            false,
        );
        assert_eq!(green.to_string(), source);
        let expected = vec![record(
            variant_role(owner, VariantDeclarationRole::NamedFieldName),
            RecoveryKind::Error,
            at..at + 1,
            0,
        )];
        assert_eq!(records, expected, "{owner:?}");
        let mut frozen = expected.clone();
        frozen[0].id = DiagnosticId(71);
        let (again, reconciled, _, _) = typed_variant(
            source,
            owner,
            VariantSequenceForm::Braced,
            false,
            0,
            700,
            None,
            Some(&frozen),
            false,
        );
        assert_eq!(again, green, "{owner:?}");
        assert_eq!(reconciled, frozen, "{owner:?}");
    }
}

#[test]
fn typed_variant_optional_shell_rejection_is_effect_free_for_both_owners() {
    // Evidence and execution in the variant recovery design requires optional
    // shell rejection to preserve input, output, and the diagnostic cursor.
    for owner in [VariantOwner::Enum, VariantOwner::Error] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new_for_test(&operators);
        let mut input = "  @ rest";
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(SyntaxKind::Root.into());
        let before = recover.diagnostic_position();
        let entry = match owner {
            VariantOwner::Enum => enum_declaration_witness,
            VariantOwner::Error => error_declaration_witness,
        };
        let exit = entry(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
            0,
            0,
            crate::statement::StatementLineHandoff::OrdinaryLayout,
            700,
            LineEntry::InLine,
            None,
        );
        assert!(exit.is_none());
        assert_eq!(input, "  @ rest");
        assert_eq!(recover.diagnostic_position(), before);
        assert_eq!(recover.recovery_slot_count(), 0);
        builder.finish_node();
        let (green, records) = (builder.finish(), recover.finish_recoveries_for_test());
        assert_eq!(green.to_string(), "");
        assert_eq!(syntax_root(green).children_with_tokens().count(), 0);
        assert!(records.is_empty());
    }
}

#[test]
fn typed_variant_records_cover_both_owners_all_forms_and_frozen_seeded_ids() {
    for owner in [VariantOwner::Enum, VariantOwner::Error] {
        for (form, source, start, end) in [
            (VariantSequenceForm::Braced, "{  @ $ 名}", 3, 6),
            (VariantSequenceForm::EqualsInline, "=  @ $ 名", 3, 6),
            (VariantSequenceForm::ColonIndented, ":\r\n  @ $ 名", 5, 8),
            (VariantSequenceForm::EqualsIndented, "=\r\n  @ $ 名", 5, 8),
        ] {
            for seeded in [false, true] {
                let (green, records, _, _) =
                    typed_variant(source, owner, form, false, 0, 700, None, None, seeded);
                assert_eq!(green.to_string(), source);
                let mut expected = Vec::new();
                if seeded {
                    expected.push(record(
                        variant_role(owner, VariantDeclarationRole::Name),
                        RecoveryKind::Missing,
                        0..0,
                        0,
                    ));
                }
                expected.push(record(
                    variant_role(owner, VariantDeclarationRole::Name),
                    RecoveryKind::Error,
                    700 + start..700 + end,
                    usize::from(seeded),
                ));
                assert_eq!(records, expected, "{source:?} {owner:?}");
                let root = syntax_root(green.clone());
                assert_eq!(
                    crate::tests::recovery_output::recovery_groups(&root)
                        .into_iter()
                        .next()
                        .unwrap()
                        .text()
                        .to_string(),
                    "@ $"
                );
                for (index, entry) in expected.iter_mut().enumerate() {
                    entry.id = DiagnosticId(17 + index as u32 * 11);
                }
                let (again, frozen, _, _) = typed_variant(
                    source,
                    owner,
                    form,
                    false,
                    0,
                    700,
                    None,
                    Some(&expected),
                    seeded,
                );
                assert_eq!(again, green);
                assert_eq!(frozen, expected);
            }
        }
    }
}

#[test]
fn typed_variant_terminal_runs_and_missing_keep_protected_items() {
    for owner in [VariantOwner::Enum, VariantOwner::Error] {
        for (source, accepted, error, missing_at) in [
            ("= @ $ ]rest", "= @ $", Some(2..5), None),
            ("= ]rest", "=", None, Some(1)),
        ] {
            let (green, records, exit, remainder) = typed_variant(
                source,
                owner,
                VariantSequenceForm::EqualsInline,
                false,
                0,
                100,
                None,
                None,
                false,
            );
            assert_eq!(green.to_string(), accepted);
            assert_eq!(remainder, "rest");
            let mut expected = Vec::new();
            if let Some(range) = error {
                expected.push(record(
                    variant_role(owner, VariantDeclarationRole::Item),
                    RecoveryKind::Error,
                    100 + range.start..100 + range.end,
                    0,
                ));
            }
            if let Some(at) = missing_at {
                expected.push(record(
                    variant_role(owner, VariantDeclarationRole::Item),
                    RecoveryKind::Missing,
                    100 + at..100 + at,
                    0,
                ));
            }
            assert_eq!(records, expected);
            let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), _)) = exit else {
                panic!("outer close pending")
            };
            assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
            assert_eq!(emit_pending_leading_text(&mut item), " ");
        }
        for (source, at) in [("=  ", 3), ("=\r\n", 3)] {
            let (green, records, _, _) = typed_variant(
                source,
                owner,
                VariantSequenceForm::EqualsInline,
                false,
                0,
                100,
                None,
                None,
                false,
            );
            assert_eq!(green.to_string(), source);
            assert_eq!(
                records,
                [record(
                    variant_role(owner, VariantDeclarationRole::Item),
                    RecoveryKind::Missing,
                    100 + at..100 + at,
                    0
                )]
            );
        }
        let (green, records, _, _) = typed_variant(
            "{ @ $  ",
            owner,
            VariantSequenceForm::Braced,
            false,
            0,
            100,
            None,
            None,
            false,
        );
        assert_eq!(green.to_string(), "{ @ $  ");
        assert_eq!(
            records,
            [
                record(
                    variant_role(owner, VariantDeclarationRole::Item),
                    RecoveryKind::Error,
                    102..105,
                    0
                ),
                record(
                    GrammarRole::ClosingDelimiter {
                        owner: ConstructRole::EnumBracedVariantBody,
                        delimiter: Delimiter::Brace
                    },
                    RecoveryKind::Missing,
                    107..107,
                    1
                )
            ]
        );
    }
}

#[test]
fn typed_variant_separators_and_with_preserve_trailing_control() {
    for owner in [VariantOwner::Enum, VariantOwner::Error] {
        let (green, records, _, _) = typed_variant(
            "{,A,,B,}",
            owner,
            VariantSequenceForm::Braced,
            false,
            0,
            0,
            None,
            None,
            false,
        );
        assert_eq!(green.to_string(), "{,A,,B,}");
        assert_eq!(
            records,
            [
                record(
                    variant_role(owner, VariantDeclarationRole::Item),
                    RecoveryKind::Missing,
                    1..1,
                    0
                ),
                record(
                    variant_role(owner, VariantDeclarationRole::Item),
                    RecoveryKind::Missing,
                    4..4,
                    1
                )
            ]
        );
        let (_, records, _, _) = typed_variant(
            "{A()B}",
            owner,
            VariantSequenceForm::Braced,
            false,
            0,
            0,
            None,
            None,
            false,
        );
        assert_eq!(
            records,
            [record(
                variant_role(owner, VariantDeclarationRole::Separator),
                RecoveryKind::Missing,
                4..4,
                0
            )]
        );
        for source in ["= A | with", "= | with"] {
            let (green, records, exit, _) = typed_variant(
                source,
                owner,
                VariantSequenceForm::EqualsInline,
                true,
                0,
                0,
                None,
                None,
                false,
            );
            assert_eq!(green.to_string(), source.trim_end_matches(" with"));
            assert!(records.is_empty());
            let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), _)) = exit else {
                panic!("with stays pending")
            };
            assert_eq!(item.payload_view().spelling(), Some("with"));
            assert_eq!(emit_pending_leading_text(&mut item), " ");
        }
    }
}

#[test]
fn typed_variant_raw_run_keeps_fence_and_contextual_stops_before_name_retry() {
    for owner in [VariantOwner::Enum, VariantOwner::Error] {
        for (yield_with, stops) in [(true, 0), (false, crate::lexical::stops::STOP_WITH)] {
            let (green, records, exit, _) = typed_variant(
                "= @ $ with",
                owner,
                VariantSequenceForm::EqualsInline,
                yield_with,
                stops,
                50,
                None,
                None,
                false,
            );
            assert_eq!(green.to_string(), "= @ $");
            assert_eq!(
                records,
                [record(
                    variant_role(owner, VariantDeclarationRole::Item),
                    RecoveryKind::Error,
                    52..55,
                    0
                )]
            );
            let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), _)) = exit else {
                panic!("with pending")
            };
            assert_eq!(item.payload_view().spelling(), Some("with"));
            assert_eq!(emit_pending_leading_text(&mut item), " ");
        }
        let fence = active_fence();
        let source = "> > = @ $\r\n> > ```\r\nouter";
        let (green, records, exit, remainder) = typed_variant(
            source,
            owner,
            VariantSequenceForm::EqualsInline,
            false,
            0,
            100,
            Some(&fence),
            None,
            false,
        );
        assert_eq!(green.to_string(), "> > = @ $");
        assert_eq!(
            records,
            [record(
                variant_role(owner, VariantDeclarationRole::Item),
                RecoveryKind::Error,
                106..109,
                0
            )]
        );
        assert_eq!(remainder, "> > ```\r\nouter");
        let Some(NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("fence pending")
        };
        let (leading, pending) = emit_terminal_leading_text(item);
        assert_eq!(leading, "\r\n");
        assert_eq!(pending.coordinate(), 111);
    }
}

#[test]
fn declaration_variants_build_all_payloads_in_all_four_forms() {
    for (form, source) in [
        (
            VariantSequenceForm::Braced,
            "{Unit, From from Pair(Int) -> Out, Named{x: T}, Tuple(U, V), Pos T U}",
        ),
        (
            VariantSequenceForm::ColonIndented,
            ":\n  Unit\n  From from Pair(Int) -> Out\n  Named{x: T}\n  Tuple(U, V)\n  Pos T U",
        ),
        (
            VariantSequenceForm::EqualsInline,
            "= Unit | From from Pair(Int) -> Out | Named{x: T} | Tuple(U, V) | Pos T U",
        ),
        (
            VariantSequenceForm::EqualsIndented,
            "=\n  Unit\n  | From from Pair(Int) -> Out\n  | Named{x: T}\n  | Tuple(U, V)\n  | Pos T U",
        ),
    ] {
        let (green, exit, _) = run_declaration_variant(source, form, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{form:?}");
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::EnumVariant), 5, "{form:?}");
        assert_eq!(count(&root, SyntaxKind::FromKw), 0, "tokens are not nodes");
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::FromKw)
                .count(),
            1,
            "{form:?}",
        );
        assert_eq!(count(&root, SyntaxKind::StructField), 3, "{form:?}");
        assert_eq!(count(&root, SyntaxKind::TypeExpression), 8, "{form:?}");
        assert_eq!(count(&root, SyntaxKind::Missing), 0, "{form:?}\n{root:#?}");
        assert_eq!(count(&root, SyntaxKind::Error), 0, "{form:?}\n{root:#?}");
        assert!(exit.is_some());
    }
}

#[test]
fn declaration_variant_separator_clusters_keep_only_real_empty_slots() {
    for (form, source, variants, missing) in [
        (VariantSequenceForm::Braced, "{,A,,B,}", 4, 2),
        (
            VariantSequenceForm::ColonIndented,
            ":\n  | A\n  || B\n  |",
            3,
            1,
        ),
        (VariantSequenceForm::EqualsInline, "= | A || B |", 3, 1),
        (
            VariantSequenceForm::EqualsIndented,
            "=\n  | A\n  || B\n  |",
            3,
            1,
        ),
    ] {
        let (green, _, _) = run_declaration_variant(source, form, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{form:?}");
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::EnumVariant), variants, "{form:?}");
        assert_eq!(
            count(&root, SyntaxKind::Missing),
            missing,
            "{form:?}\n{root:#?}"
        );
    }
}

#[test]
fn declaration_variant_layout_separates_same_block_and_keeps_deeper_payloads() {
    for (form, source) in [
        (VariantSequenceForm::ColonIndented, ":\n  A T\n    U\n  B"),
        (VariantSequenceForm::EqualsIndented, "=\n  A T\n    U\n  B"),
        (VariantSequenceForm::Braced, "{\n  A T\n    U\n  B\n}"),
    ] {
        let (green, _, _) = run_declaration_variant(source, form, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{form:?}");
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::EnumVariant), 2, "{form:?}");
        assert_eq!(count(&root, SyntaxKind::TypeExpression), 2, "{form:?}");
        assert_eq!(count(&root, SyntaxKind::Missing), 0, "{form:?}\n{root:#?}");
    }
}

#[test]
fn equals_inline_keeps_strictly_deeper_payload_lines_before_the_next_pipe() {
    let source = "= A T\n  U | B";
    let (green, _, _) = run_declaration_variant(
        source,
        VariantSequenceForm::EqualsInline,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), source);
    let root = syntax_root(green);
    let variants = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::EnumVariant)
        .collect::<Vec<_>>();
    assert_eq!(variants.len(), 2, "{root:#?}");
    assert_eq!(identifier_texts(&variants[0]), ["A", "T", "U"]);
    assert_eq!(count(&variants[0], SyntaxKind::TypeExpression), 2);
    assert_eq!(identifier_texts(&variants[1]), ["B"]);
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Error), 0, "{root:#?}");
}

#[test]
fn braced_pipe_recovers_inside_the_payload_instead_of_separating_variants() {
    let source = "{A T | U, B}";
    let (green, _, _) = run_declaration_variant(
        source,
        VariantSequenceForm::Braced,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), source);
    let root = syntax_root(green);
    let variants = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::EnumVariant)
        .collect::<Vec<_>>();
    assert_eq!(variants.len(), 2, "{root:#?}");
    assert_eq!(identifier_texts(&variants[0]), ["A", "T", "U"]);
    assert_eq!(count(&variants[0], SyntaxKind::TypeExpression), 2);
    assert_eq!(count(&variants[0], SyntaxKind::Error), 1, "{root:#?}");
    assert_eq!(identifier_texts(&variants[1]), ["B"]);
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
}

#[test]
fn declaration_variant_payload_recovery_stops_once_at_the_outer_pipe() {
    let (green, _, _) = run_declaration_variant(
        "= A from | B | C @ | D",
        VariantSequenceForm::EqualsInline,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "= A from | B | C @ | D");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::EnumVariant), 4, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Error), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::TypeExpression), 1, "{root:#?}");
}

#[test]
fn declaration_variant_outer_pipe_separates_all_non_braced_forms() {
    for (form, source) in [
        (VariantSequenceForm::ColonIndented, ":\n  A from T | B"),
        (VariantSequenceForm::EqualsInline, "= A from T | B"),
        (VariantSequenceForm::EqualsIndented, "=\n  A from T\n  | B"),
    ] {
        let (green, _, _) = run_declaration_variant(source, form, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{form:?}");
        let root = syntax_root(green);
        assert_eq!(
            count(&root, SyntaxKind::EnumVariant),
            2,
            "{form:?}\n{root:#?}"
        );
        assert_eq!(count(&root, SyntaxKind::Error), 0, "{form:?}\n{root:#?}");
        assert_eq!(count(&root, SyntaxKind::Missing), 0, "{form:?}\n{root:#?}");
    }
}

#[test]
fn declaration_variant_outer_pipe_is_suspended_inside_nested_type_episodes() {
    for (source, groups) in [("= A from (T | U) | B", 1), ("= A from ((T | U)) | B", 2)] {
        let (green, _, _) = run_declaration_variant(
            source,
            VariantSequenceForm::EqualsInline,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), source);
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::EnumVariant), 2, "{root:#?}");
        assert_eq!(
            count(&root, SyntaxKind::ParenthesizedTypeGroup),
            groups,
            "{root:#?}"
        );
        assert_eq!(count(&root, SyntaxKind::Error), 1, "{root:#?}");
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Pipe
                    || (token.kind() == SyntaxKind::Error && token.text() == "|"))
                .count(),
            2,
        );
    }
}

#[test]
fn declaration_variant_contextual_pipe_stays_local_to_each_nested_type_owner() {
    for (source, owner) in [
        ("= A from (| T) | B", SyntaxKind::ParenthesizedTypeGroup),
        ("= A from (T | U) | B", SyntaxKind::ParenthesizedTypeGroup),
        ("= A from F(| T) | B", SyntaxKind::TypeCallTail),
        ("= A from F(T | U) | B", SyntaxKind::TypeCallTail),
        ("= A from [| T] -> X | B", SyntaxKind::BracketRow),
        ("= A from [T | U] -> X | B", SyntaxKind::BracketRow),
        ("= A from (T -> | U) | B", SyntaxKind::TypeArrowTail),
        ("= A from (T -> U | V) | B", SyntaxKind::TypeArrowTail),
        ("= A from (for 'a: | T) | B", SyntaxKind::ForallType),
        ("= A from (for 'a: T | U) | B", SyntaxKind::ForallType),
        ("= A from {x: | T} | B", SyntaxKind::NamedRecordType),
        ("= A from {x: T | U} | B", SyntaxKind::NamedRecordType),
        ("= A from '[| T] | B", SyntaxKind::EffectRowType),
        ("= A from '[T | U] | B", SyntaxKind::EffectRowType),
        (
            "= A from :{Tag | T} | B",
            SyntaxKind::PolymorphicVariantType,
        ),
        (
            "= A from :{Tag T | U} | B",
            SyntaxKind::PolymorphicVariantType,
        ),
        ("= A from (@ | T) | B", SyntaxKind::ParenthesizedTypeGroup),
    ] {
        let (green, _, _) = run_declaration_variant(
            source,
            VariantSequenceForm::EqualsInline,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), source, "{source:?}");
        let root = syntax_root(green);
        assert_eq!(
            count(&root, SyntaxKind::EnumVariant),
            2,
            "{source:?}\n{root:#?}"
        );
        assert!(
            root.descendants().any(|node| node.kind() == owner),
            "{source:?}\n{root:#?}"
        );
        assert!(
            count(&root, SyntaxKind::Error) >= 1,
            "{source:?}\n{root:#?}"
        );
        let bars = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.text() == "|")
            .collect::<Vec<_>>();
        assert_eq!(bars.len(), 2, "{source:?}\n{root:#?}");
        assert_eq!(bars[0].kind(), SyntaxKind::Error, "{source:?}\n{root:#?}");
        assert!(
            bars[0]
                .parent_ancestors()
                .any(|node| node.kind() == SyntaxKind::EnumVariant),
            "{source:?}\n{root:#?}"
        );
        assert_eq!(bars[1].kind(), SyntaxKind::Pipe, "{source:?}\n{root:#?}");
        assert_eq!(
            bars[1].parent().unwrap().kind(),
            SyntaxKind::Root,
            "{source:?}\n{root:#?}"
        );
    }
}

#[test]
fn braced_variant_fields_keep_contextual_pipe_as_local_malformed_type_input() {
    for source in ["{A{x: | T}, B}", "{A{x: T | U}, B}"] {
        let (green, _, _) = run_declaration_variant(
            source,
            VariantSequenceForm::Braced,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), source);
        let root = syntax_root(green);
        assert_eq!(
            count(&root, SyntaxKind::EnumVariant),
            2,
            "{source:?}\n{root:#?}"
        );
        assert!(
            count(&root, SyntaxKind::Error) >= 1,
            "{source:?}\n{root:#?}"
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Pipe
                    || (token.kind() == SyntaxKind::Error && token.text() == "|"))
                .count(),
            1,
            "{source:?}\n{root:#?}",
        );
    }
}

#[test]
fn malformed_named_payload_retry_keeps_pipe_lexical_and_converges_at_outer_comma() {
    let source = "{A{@ | x:T}, B}";
    let (green, exit, _) = run_declaration_variant(
        source,
        VariantSequenceForm::Braced,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(NormalizedExit::Complete(Ok(()), _))));

    let root = syntax_root(green);
    let variants = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::EnumVariant)
        .collect::<Vec<_>>();
    assert_eq!(variants.len(), 2, "{root:#?}");
    assert_eq!(identifier_texts(&variants[0]), ["A", "x", "T"]);
    assert_eq!(count(&variants[0], SyntaxKind::StructField), 2, "{root:#?}");
    assert_eq!(count(&variants[0], SyntaxKind::Error), 1, "{root:#?}");
    assert_eq!(identifier_texts(&variants[1]), ["B"]);
    let pipes = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| {
            token.kind() == SyntaxKind::Pipe
                || (token.kind() == SyntaxKind::Error && token.text() == "|")
        })
        .collect::<Vec<_>>();
    assert_eq!(pipes.len(), 1, "{root:#?}");
    assert!(
        pipes[0]
            .parent_ancestors()
            .any(|node| node.kind() == SyntaxKind::StructField),
        "{root:#?}",
    );
    assert!(pipes[0].kind() == SyntaxKind::Error, "{root:#?}",);
}

#[test]
fn type_apply_argument_keeps_local_pipe_lexical_before_outer_variant_pipe() {
    let source = "= A from F T::|U | B";
    let (green, _, _) = run_declaration_variant(
        source,
        VariantSequenceForm::EqualsInline,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), source);

    let root = syntax_root(green);
    let variants = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::EnumVariant)
        .collect::<Vec<_>>();
    assert_eq!(variants.len(), 2, "{root:#?}");
    assert_eq!(identifier_texts(&variants[0]), ["A", "F", "T", "U"]);
    assert_eq!(count(&variants[0], SyntaxKind::TypeApplyArgument), 1);
    assert_eq!(count(&variants[0], SyntaxKind::TypePathTail), 1);
    assert_eq!(count(&variants[0], SyntaxKind::Error), 1, "{root:#?}");
    assert_eq!(identifier_texts(&variants[1]), ["B"]);
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
    let pipes = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| {
            token.kind() == SyntaxKind::Pipe
                || (token.kind() == SyntaxKind::Error && token.text() == "|")
        })
        .collect::<Vec<_>>();
    assert_eq!(pipes.len(), 2, "{root:#?}");
    assert!(
        pipes[0]
            .parent_ancestors()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument),
        "{root:#?}",
    );
    assert!(pipes[0].kind() == SyntaxKind::Error, "{root:#?}",);
    assert!(
        !pipes[1]
            .parent_ancestors()
            .any(|node| node.kind() == SyntaxKind::TypeExpression),
        "{root:#?}",
    );
}

#[test]
fn completed_type_path_returns_same_episode_pipe_to_variant_owner() {
    let source = "= A from T::U | B";
    let (green, _, _) = run_declaration_variant(
        source,
        VariantSequenceForm::EqualsInline,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), source);

    let root = syntax_root(green);
    let variants = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::EnumVariant)
        .collect::<Vec<_>>();
    assert_eq!(variants.len(), 2, "{root:#?}");
    assert_eq!(identifier_texts(&variants[0]), ["A", "T", "U"]);
    assert_eq!(count(&variants[0], SyntaxKind::TypePathTail), 1);
    assert_eq!(identifier_texts(&variants[1]), ["B"]);
    assert_eq!(count(&root, SyntaxKind::Error), 0, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
    let pipes = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| {
            token.kind() == SyntaxKind::Pipe
                || (token.kind() == SyntaxKind::Error && token.text() == "|")
        })
        .collect::<Vec<_>>();
    assert_eq!(pipes.len(), 1, "{root:#?}");
    assert!(
        !pipes[0]
            .parent_ancestors()
            .any(|node| node.kind() == SyntaxKind::TypeExpression),
        "{root:#?}",
    );
}

#[test]
fn declaration_variant_indented_dedent_remains_one_pending_item() {
    for (form, source, accepted) in [
        (VariantSequenceForm::ColonIndented, ":\n  A\nnext", ":\n  A"),
        (
            VariantSequenceForm::EqualsIndented,
            "=\n  A\r\nnext",
            "=\n  A",
        ),
        (VariantSequenceForm::EqualsInline, "= A\nnext", "= A"),
    ] {
        let (green, exit, _) = run_declaration_variant(source, form, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), accepted, "{form:?}");
        let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), _)) = exit else {
            panic!("dedent must remain pending: {form:?}")
        };
        assert_eq!(item.payload_view().spelling(), Some("next"));
        assert_eq!(
            emit_pending_leading_text(&mut item),
            if source.contains("\r\n") {
                "\r\n"
            } else {
                "\n"
            },
            "{form:?}",
        );
    }
}

#[test]
fn declaration_variant_fields_borrow_outer_closes_after_local_missing_close() {
    let (green, exit, _) = run_declaration_variant(
        "{A(T}",
        VariantSequenceForm::Braced,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "{A(T}");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::EnumVariant), 1);
    assert_eq!(count(&root, SyntaxKind::StructField), 1);
    assert_eq!(count(&root, SyntaxKind::Missing), 1, "{root:#?}");
    assert!(matches!(exit, Some(NormalizedExit::Complete(Ok(()), _))));

    let (green, exit, _) = run_declaration_variant(
        "= A{x:T)",
        VariantSequenceForm::EqualsInline,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "= A{x:T");
    let Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) = exit else {
        panic!("outer close must remain the exact pending Item")
    };
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::RParen));
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::Missing), 1, "{root:#?}");
}

#[test]
fn declaration_variant_field_local_close_missing_preserves_borrowed_close_cst() {
    use SyntaxKind::{
        Error, Invalid, LBrace, LParen, Missing, StructField, StructFieldForeignClose,
    };
    for owner in [VariantOwner::Enum, VariantOwner::Error] {
        for (source, accepted, open, field_end, pending_kind, leading) in [
            ("= A{x:T)", "= A{x:T", LBrace, 7, TokenKind::RParen, ""),
            ("= A(T]", "= A(T", LParen, 5, TokenKind::RBracket, ""),
            (
                "= A(T \r\n ]",
                "= A(T",
                LParen,
                5,
                TokenKind::RBracket,
                " \r\n ",
            ),
        ] {
            if matches!(owner, VariantOwner::Error) && !leading.is_empty() {
                continue;
            }
            let (green, _, exit, remainder) = typed_variant(
                source,
                owner,
                VariantSequenceForm::EqualsInline,
                false,
                0,
                100,
                None,
                None,
                false,
            );
            assert_eq!(green.to_string(), accepted, "{owner:?} {source:?}");
            assert_eq!(remainder, "");
            let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), _)) = exit else {
                panic!("foreign close must stay pending")
            };
            assert_eq!(item.payload_view().token_kind(), Some(pending_kind));
            assert_eq!(emit_pending_leading_text(&mut item), leading);
            let root = syntax_root(green);
            assert_eq!(count(&root, SyntaxKind::EnumVariant), 1);
            let variant = root
                .children()
                .find(|node| node.kind() == SyntaxKind::EnumVariant)
                .unwrap();
            assert_eq!(variant.parent().as_ref(), Some(&root));
            assert_eq!(root.kind(), SyntaxKind::Root);
            assert_eq!(
                variant
                    .children_with_tokens()
                    .skip_while(|element| element.kind() != open)
                    .map(|element| (
                        element.kind(),
                        element.as_node().is_some(),
                        usize::from(element.text_range().start())
                            ..usize::from(element.text_range().end()),
                        element.to_string(),
                    ))
                    .collect::<Vec<_>>(),
                [
                    (open, false, 3..4, accepted[3..4].to_owned()),
                    (StructField, true, 4..field_end, accepted[4..].to_owned()),
                    (Missing, true, field_end..field_end, String::new()),
                ]
            );
            let missing = root
                .descendants()
                .filter(|node| node.kind() == Missing)
                .collect::<Vec<_>>();
            assert_eq!(missing.len(), 1);
            assert_eq!(missing[0].parent().as_ref(), Some(&variant));
            assert!(missing[0].children_with_tokens().next().is_none());
            assert_eq!(count(&root, StructField), 1);
            assert!(root.descendants_with_tokens().all(|element| !matches!(
                element.kind(),
                Error | Invalid | StructFieldForeignClose
            )));
        }
    }
}

#[test]
fn declaration_variant_hands_raw_close_and_fence_boundary_up_exactly() {
    let (green, exit, _) = run_declaration_variant(
        "= A}",
        VariantSequenceForm::EqualsInline,
        91,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "= A");
    let Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) = exit else {
        panic!("caller close must stay pending")
    };
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::RBrace));

    let fence = active_fence();
    let accepted = "> > = A";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let origin = 700;
    let (green, exit, remainder) = run_declaration_variant(
        &source,
        VariantSequenceForm::EqualsInline,
        origin,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let Some(NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart)) = exit
    else {
        panic!("fence close must stay pending with its line-entry fact")
    };
    let boundary = item.payload_view();
    assert!(boundary.is_boundary());
    let (leading, pending) = emit_terminal_leading_text(item);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));
    let root = syntax_root(green);
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
            .count(),
        1,
    );
}

#[test]
fn shared_field_extraction_preserves_struct_named_and_tuple_shapes() {
    for (source, fields) in [
        ("struct S{x:T, y:U}", 2),
        ("struct S(T, U)", 2),
        ("struct S{x:T] y:U}", 2),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::StructField), fields, "{source:?}");
    }
}

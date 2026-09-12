use crate::tests::support::*;

// Composition witnesses use kind, identity, parent and byte extent. Error
// spelling is opaque; native spelling is checked only for non-Error tokens.
pub(super) fn assert_sequence_composition_children(
    owner: &SyntaxNode,
    start: usize,
    expected: &[(SyntaxKind, usize)],
    source: &str,
) {
    use SyntaxKind::{
        DeclarationCompanion, Missing, StructField, StructFieldForeignClose, TypeExpression,
    };
    let children = owner
        .children_with_tokens()
        .skip_while(|child| usize::from(child.text_range().start()) < start)
        .collect::<Vec<_>>();
    assert_eq!(children.len(), expected.len(), "{source:?}\n{owner:#?}");
    let mut at = start;
    for (child, &(kind, len)) in children.iter().zip(expected) {
        assert_eq!(child.parent().as_ref(), Some(owner));
        assert_eq!(child.kind(), kind, "{source:?}");
        assert_eq!(
            child.as_node().is_some(),
            matches!(
                kind,
                DeclarationCompanion
                    | Missing
                    | StructField
                    | StructFieldForeignClose
                    | TypeExpression
            )
        );
        assert_eq!(
            usize::from(child.text_range().start())..usize::from(child.text_range().end()),
            at..at + len
        );
        if kind == Missing {
            assert_eq!(len, 0);
            assert!(
                child
                    .as_node()
                    .unwrap()
                    .children_with_tokens()
                    .next()
                    .is_none()
            );
        } else if kind != SyntaxKind::Error && child.as_token().is_some() {
            assert_eq!(child.to_string(), source[at..at + len]);
        }
        at += len;
    }
}

pub(super) fn assert_composition_field_ancestry(field: &SyntaxNode, declaration: SyntaxKind) {
    let mut expected = vec![SyntaxKind::StructField];
    if declaration != SyntaxKind::StructDeclaration {
        expected.push(SyntaxKind::EnumVariant);
    }
    expected.extend([declaration, SyntaxKind::Statement, SyntaxKind::Root]);
    assert_eq!(
        field.ancestors().map(|n| n.kind()).collect::<Vec<_>>(),
        expected
    );
}

pub(super) fn assert_delimited_field_sequence_composition(
    prefix: &str,
    suffix: &str,
    declaration: SyntaxKind,
) {
    use SyntaxKind::{
        Colon, Comma, Error, Identifier, LBrace, LParen, Missing, RBrace, StructField,
        TypeExpression, Whitespace,
    };
    let named = prefix.ends_with('{');
    let body = if named {
        "@ x:T,@:U,y @ V;z W"
    } else {
        "T U,=V,"
    };
    let source = format!("{prefix}{body}{}", if named { suffix } else { "" });
    let (green, exit) = run_statement(&source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let fields = root
        .descendants()
        .filter(|n| n.kind() == StructField)
        .collect::<Vec<_>>();
    let sequence = fields[0].parent().unwrap();
    assert_eq!(fields.len(), if named { 5 } else { 3 });
    for field in &fields {
        assert_composition_field_ancestry(field, declaration);
        assert_eq!(field.parent().as_ref(), Some(&sequence));
    }
    let start = prefix.len();
    if named {
        assert_sequence_composition_children(
            &sequence,
            start - 1,
            &[
                (LBrace, 1),
                (StructField, 1),
                (Whitespace, 1),
                (Missing, 0),
                (StructField, 3),
                (Comma, 1),
                (StructField, 3),
                (Comma, 1),
                (StructField, 5),
                (Error, 1),
                (StructField, 3),
                (RBrace, 1),
            ],
            &source,
        );
        for (field, offset, children) in [
            (&fields[0], 0, vec![(Error, 1)]),
            (
                &fields[1],
                2,
                vec![(Identifier, 1), (Colon, 1), (TypeExpression, 1)],
            ),
            (
                &fields[2],
                6,
                vec![(Error, 1), (Colon, 1), (TypeExpression, 1)],
            ),
            (
                &fields[3],
                10,
                vec![
                    (Identifier, 1),
                    (Whitespace, 1),
                    (Error, 1),
                    (TypeExpression, 2),
                ],
            ),
            (
                &fields[4],
                16,
                vec![
                    (Identifier, 1),
                    (Whitespace, 1),
                    (Missing, 0),
                    (TypeExpression, 1),
                ],
            ),
        ] {
            assert_sequence_composition_children(field, start + offset, &children, &source);
        }
        let occurrences = root
            .descendants_with_tokens()
            .filter(|e| matches!(e.kind(), Error | Missing))
            .map(|e| (e.kind(), e.parent().unwrap()))
            .collect::<Vec<_>>();
        assert_eq!(
            occurrences,
            vec![
                (Error, fields[0].clone()),
                (Missing, sequence.clone()),
                (Error, fields[2].clone()),
                (Error, fields[3].clone()),
                (Error, sequence.clone()),
                (Missing, fields[4].clone()),
            ]
        );
    } else {
        assert_sequence_composition_children(
            &sequence,
            start - 1,
            &[
                (LParen, 1),
                (StructField, 3),
                (Comma, 1),
                (StructField, 2),
                (Comma, 1),
                (StructField, 0),
                (Missing, 0),
            ],
            &source,
        );
        assert_sequence_composition_children(&fields[0], start, &[(TypeExpression, 3)], &source);
        assert_eq!(
            fields[0]
                .descendants()
                .filter(|n| n.kind() == SyntaxKind::TypeApplyArgument)
                .count(),
            1
        );
        assert_sequence_composition_children(
            &fields[1],
            start + 4,
            &[(Error, 1), (TypeExpression, 1)],
            &source,
        );
        assert_sequence_composition_children(
            &fields[2],
            source.len(),
            &[(TypeExpression, 0)],
            &source,
        );
        let ty = fields[2].first_child().unwrap();
        assert_sequence_composition_children(&ty, source.len(), &[(Missing, 0)], &source);
        let missing = root
            .descendants()
            .filter(|n| n.kind() == Missing)
            .collect::<Vec<_>>();
        let variant = declaration != SyntaxKind::StructDeclaration;
        assert_eq!(missing.len(), if variant { 3 } else { 2 });
        assert_eq!(missing[0].parent().as_ref(), Some(&ty));
        assert_eq!(missing[1].parent().as_ref(), Some(&sequence));
        assert_eq!(fields[2].next_sibling().as_ref(), Some(&missing[1]));
        if variant {
            assert_eq!(missing[2].parent(), sequence.parent());
            assert_eq!(missing[2].parent().unwrap().kind(), declaration);
            assert_eq!(sequence.next_sibling().as_ref(), Some(&missing[2]));
        }
        for node in missing {
            assert_eq!(usize::from(node.text_range().start()), source.len());
            assert!(node.text_range().is_empty());
        }
    }
    assert!(!root.descendants().any(|n| matches!(
        n.kind(),
        SyntaxKind::Invalid | SyntaxKind::StructFieldForeignClose
    )));
}

#[test]
fn struct_delimited_field_sequence_composes_ordered_occurrences() {
    assert_delimited_field_sequence_composition("struct S{", "}", SyntaxKind::StructDeclaration);
    assert_delimited_field_sequence_composition("struct S(", ")", SyntaxKind::StructDeclaration);
}

pub(super) fn assert_matching_tuple_composition(
    root: &SyntaxNode,
    start: usize,
    declaration: SyntaxKind,
    source: &str,
) -> SyntaxNode {
    use SyntaxKind::{Error, StructField, TypeExpression};
    let fields = root
        .descendants()
        .filter(|n| n.kind() == StructField)
        .collect::<Vec<_>>();
    assert_eq!(fields.len(), 2);
    for field in &fields {
        assert_composition_field_ancestry(field, declaration);
    }
    let owner = fields[0].parent().unwrap();
    assert_eq!(fields[1].parent().as_ref(), Some(&owner));
    assert_sequence_composition_children(&fields[0], start, &[(TypeExpression, 3)], source);
    assert_eq!(
        fields[0]
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::TypeApplyArgument)
            .count(),
        1
    );
    assert_sequence_composition_children(
        &fields[1],
        start + 4,
        &[(Error, 1), (TypeExpression, 1)],
        source,
    );
    assert!(!root.descendants().any(|n| matches!(
        n.kind(),
        SyntaxKind::Missing | SyntaxKind::Invalid | SyntaxKind::StructFieldForeignClose
    )));
    owner
}

#[test]
fn struct_tuple_field_sequence_matching_close_attaches_companion() {
    use SyntaxKind::{Comma, DeclarationCompanion, LParen, RParen, StructDeclaration, StructField};
    let source = "struct S(T U,=V) with {} outer tail";
    let (green, exit, remainder) = run_statement_normalized(source, 0, LineEntry::InLine, None);
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Ok(()), LineEntry::InLine)
    ));
    assert_eq!(green.to_string(), "struct S(T U,=V) with {}");
    assert_eq!(remainder, " outer tail");
    let root = SyntaxNode::new_root(green);
    let owner = assert_matching_tuple_composition(&root, 9, StructDeclaration, source);
    assert_sequence_composition_children(
        &owner,
        8,
        &[
            (LParen, 1),
            (StructField, 3),
            (Comma, 1),
            (StructField, 2),
            (RParen, 1),
            (DeclarationCompanion, 8),
        ],
        source,
    );
}

#[test]
fn struct_delimited_field_sequence_separates_foreign_close_and_terminal_missing() {
    use SyntaxKind::{Error, LBrace, Missing, StructField, StructFieldForeignClose};
    let source = "struct 名{x:T;])";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let owner = root
        .descendants()
        .find(|n| n.kind() == SyntaxKind::StructDeclaration)
        .unwrap();
    assert_sequence_composition_children(
        &owner,
        10,
        &[
            (LBrace, 1),
            (StructField, 3),
            (Error, 1),
            (StructFieldForeignClose, 2),
            (Missing, 0),
        ],
        source,
    );
    let wrappers = root
        .descendants()
        .filter(|n| n.kind() == StructFieldForeignClose)
        .collect::<Vec<_>>();
    assert_eq!(wrappers.len(), 1);
    assert_sequence_composition_children(&wrappers[0], 15, &[(Error, 1), (Error, 1)], source);
    assert_eq!(
        root.descendants().filter(|n| n.kind() == Missing).count(),
        1
    );
    assert!(!root.descendants().any(|n| n.kind() == SyntaxKind::Invalid));
}

// Header evidence uses only direct Rowan children and byte ranges. In particular,
// adjacent Error fragments stay opaque; native retry trivia ends their group.
fn assert_struct_schema_header(source: &str, expected: &[(SyntaxKind, std::ops::Range<usize>)]) {
    let (green, _, _) = run_statement_normalized(source, 0, LineEntry::InLine, None);
    let root = SyntaxNode::new_root(green);
    let statement = root.first_child().expect("Statement");
    assert_eq!(statement.kind(), SyntaxKind::Statement);
    assert_eq!(statement.parent(), Some(root.clone()));
    let owner = statement.first_child().expect("StructDeclaration");
    assert_eq!(owner.kind(), SyntaxKind::StructDeclaration);
    assert_eq!(owner.parent(), Some(statement));
    // Colon starts an indented field body. Its following children belong to
    // the separate field schema; this witness stops at the native starter.
    let header_len = if expected
        .last()
        .is_some_and(|(kind, _)| *kind == SyntaxKind::Colon)
    {
        expected.len()
    } else {
        usize::MAX
    };
    let actual = owner
        .children_with_tokens()
        .take(header_len)
        .map(|child| {
            assert_eq!(child.parent(), Some(owner.clone()));
            if child.kind() == SyntaxKind::Missing {
                assert!(
                    child
                        .as_node()
                        .unwrap()
                        .children_with_tokens()
                        .next()
                        .is_none()
                );
            } else {
                assert!(child.as_token().is_some());
            }
            (
                child.kind(),
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(actual, expected, "{source:?}");
    assert!(
        !root
            .descendants_with_tokens()
            .any(|child| child.kind() == SyntaxKind::Invalid)
    );
}

#[test]
fn struct_schema_name_missing_terminal_and_retry() {
    use SyntaxKind::{Error, Identifier, LBrace, Missing, RBrace, Semicolon, StructKw, Whitespace};
    assert_struct_schema_header("struct", &[(StructKw, 0..6), (Missing, 6..6)]);
    assert_struct_schema_header(
        "struct  ",
        &[(StructKw, 0..6), (Whitespace, 6..8), (Missing, 8..8)],
    );
    for suffix in ["", "  ", "  ]tail", "\r\nnext"] {
        assert_struct_schema_header(
            &format!("struct @ #{suffix}"),
            &[
                (StructKw, 0..6),
                (Whitespace, 6..7),
                (Error, 7..8),
                (Error, 8..9),
                (Error, 9..10),
            ],
        );
    }
    assert_struct_schema_header(
        "struct @ # 名;",
        &[
            (StructKw, 0..6),
            (Whitespace, 6..7),
            (Error, 7..8),
            (Error, 8..9),
            (Error, 9..10),
            (Whitespace, 10..11),
            (Identifier, 11..14),
            (Semicolon, 14..15),
        ],
    );
    assert_struct_schema_header(
        "struct ;",
        &[
            (StructKw, 0..6),
            (Missing, 6..6),
            (Whitespace, 6..7),
            (Semicolon, 7..8),
        ],
    );
    assert_struct_schema_header(
        "struct {}",
        &[
            (StructKw, 0..6),
            (Missing, 6..6),
            (Whitespace, 6..7),
            (LBrace, 7..8),
            (RBrace, 8..9),
        ],
    );
    for suffix in ["  ]tail", "\r\nnext"] {
        assert_struct_schema_header(
            &format!("struct{suffix}"),
            &[(StructKw, 0..6), (Missing, 6..6)],
        );
    }
}

#[test]
fn struct_schema_body_introducer_missing_terminal_and_native_retry() {
    use SyntaxKind::{
        Colon, Error, Identifier, LBrace, LParen, Missing, RBrace, RParen, Semicolon, StructKw,
        Whitespace,
    };
    let header = vec![(StructKw, 0..6), (Whitespace, 6..7), (Identifier, 7..10)];
    for (suffix, tail) in [
        ("", vec![(Missing, 10..10)]),
        ("  ", vec![(Whitespace, 10..12), (Missing, 12..12)]),
        (" Foo", vec![(Whitespace, 10..11), (Missing, 11..11)]),
        ("  ]tail", vec![(Missing, 10..10)]),
        ("\r\nnext", vec![(Missing, 10..10)]),
    ] {
        let mut expected = header.clone();
        expected.extend(tail);
        assert_struct_schema_header(&format!("struct 名{suffix}"), &expected);
    }
    let mut malformed = header;
    malformed.extend([
        (Whitespace, 10..11),
        (Error, 11..12),
        (Error, 12..13),
        (Error, 13..14),
    ]);
    for suffix in ["", "  ", "  ]tail", "\r\nnext"] {
        assert_struct_schema_header(&format!("struct 名 @ #{suffix}"), &malformed);
    }
    for (body, native) in [
        (";", vec![(Semicolon, 15..16)]),
        ("{}", vec![(LBrace, 15..16), (RBrace, 16..17)]),
        ("()", vec![(LParen, 15..16), (RParen, 16..17)]),
        (":", vec![(Colon, 15..16)]),
    ] {
        let mut expected = malformed.clone();
        expected.push((Whitespace, 14..15));
        expected.extend(native);
        assert_struct_schema_header(&format!("struct 名 @ # {body}"), &expected);
    }
}

pub(super) fn assert_field_separators_cst(prefix: &str, suffix: &str, ancestors: &[SyntaxKind]) {
    use SyntaxKind::{Comma, Error, Missing, StructField, TypeExpression, Whitespace};
    let tuple = prefix.ends_with('(');
    let (open, close, first, next) = if tuple {
        (SyntaxKind::LParen, SyntaxKind::RParen, "T", "U")
    } else {
        (SyntaxKind::LBrace, SyntaxKind::RBrace, "x:T", "y:U")
    };
    // The tuple missing-separator witness retries required Type at Equals;
    // its Error remains inside the next field, independently of Separator.
    let missing_next = if tuple { "=U" } else { next };
    for (between, successor, middle, missing, errors) in [
        (
            " ",
            missing_next,
            vec![(Whitespace, " "), (Missing, "")],
            1,
            usize::from(tuple),
        ),
        (
            "; ; ",
            next,
            vec![(Error, ";"), (Error, " "), (Error, ";"), (Whitespace, " ")],
            0,
            3,
        ),
        (",", next, vec![(Comma, ",")], 0, 0),
        ("\n", next, vec![(SyntaxKind::Newline, "\n")], 0, 0),
        (
            ";,",
            next,
            vec![(Error, ";"), (StructField, ""), (Comma, ",")],
            1,
            1,
        ),
        ("; ", "", vec![(Error, ";"), (Whitespace, " ")], 0, 1),
    ] {
        let source = format!("{prefix}{first}{between}{successor}{suffix}");
        let (green, exit) = run_statement(&source);
        assert_eq!(green.to_string(), source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        let fields = root
            .descendants()
            .filter(|node| node.kind() == StructField)
            .collect::<Vec<_>>();
        let sequence = fields[0].parent().unwrap();
        for field in &fields {
            assert_eq!(field.parent().as_ref(), Some(&sequence));
            assert_eq!(
                field
                    .ancestors()
                    .skip(1)
                    .take(ancestors.len())
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                ancestors
            );
        }
        let mut expected = vec![(open, &prefix[prefix.len() - 1..]), (StructField, first)];
        expected.extend(middle);
        if !successor.is_empty() {
            expected.push((StructField, successor));
        }
        expected.push((close, &suffix[..1]));
        let mut offset = prefix.len() - 1;
        let expected = expected
            .into_iter()
            .map(|(kind, text)| {
                let range = offset..offset + text.len();
                offset = range.end;
                (kind, range, text.to_owned())
            })
            .collect::<Vec<_>>();
        assert_eq!(
            sequence
                .children_with_tokens()
                .skip_while(|element| element.kind() != open)
                .map(|element| {
                    if element.kind() == Error {
                        assert!(element.as_token().is_some());
                    }
                    if element.kind() == Missing {
                        assert_eq!(element.as_node().unwrap().children_with_tokens().count(), 0);
                    }
                    (
                        element.kind(),
                        usize::from(element.text_range().start())
                            ..usize::from(element.text_range().end()),
                        element.to_string(),
                    )
                })
                .collect::<Vec<_>>(),
            expected,
            "{source:?}\n{root:#?}"
        );
        assert_eq!(
            fields.len(),
            1 + usize::from(!successor.is_empty()) + usize::from(between == ";,")
        );
        if between == ";," {
            let at = prefix.len() + first.len() + 1;
            if tuple {
                assert_field_item_children(&fields[1], at, &[(TypeExpression, "")]);
                assert_field_item_children(&fields[1].first_child().unwrap(), at, &[(Missing, "")]);
            } else {
                assert_field_item_children(&fields[1], at, &[(Missing, "")]);
            }
        }
        if tuple && between == " " {
            assert_field_item_children(
                &fields[1],
                prefix.len() + first.len() + between.len(),
                &[(Error, "="), (TypeExpression, "U")],
            );
        }
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == Missing)
                .count(),
            missing,
            "{source:?}"
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|element| element.kind() == Error)
                .count(),
            errors,
            "{source:?}"
        );
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Invalid)
        );
    }
}

#[test]
fn struct_field_separators_have_direct_cst_slots() {
    for (prefix, suffix) in [("struct S{", "}"), ("struct S(", ")")] {
        assert_field_separators_cst(prefix, suffix, &[SyntaxKind::StructDeclaration]);
    }
}

#[test]
fn struct_indented_field_separator_error_has_direct_cst_slot() {
    use SyntaxKind::{Colon, Error, Newline, StructDeclaration, StructField, Whitespace};

    let source = "struct S:\n  x:T;\n  y:U";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let declaration = root
        .descendants()
        .find(|node| node.kind() == StructDeclaration)
        .unwrap();
    let fields = root
        .descendants()
        .filter(|node| node.kind() == StructField)
        .collect::<Vec<_>>();
    assert_eq!(fields.len(), 2);
    for field in fields {
        assert_eq!(field.parent().as_ref(), Some(&declaration));
    }
    assert_eq!(
        declaration
            .children_with_tokens()
            .skip_while(|element| element.kind() != Colon)
            .map(|element| {
                assert_eq!(element.as_node().is_some(), element.kind() == StructField);
                (
                    element.kind(),
                    usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end()),
                    element.to_string(),
                )
            })
            .collect::<Vec<_>>(),
        vec![
            (Colon, 8..9, ":".to_owned()),
            (Newline, 9..10, "\n".to_owned()),
            (Whitespace, 10..12, "  ".to_owned()),
            (StructField, 12..15, "x:T".to_owned()),
            (Error, 15..16, ";".to_owned()),
            (Newline, 16..17, "\n".to_owned()),
            (Whitespace, 17..19, "  ".to_owned()),
            (StructField, 19..22, "y:U".to_owned()),
        ]
    );
    let mut previous_error = false;
    let error_groups = declaration
        .children_with_tokens()
        .filter(|element| {
            let error = element.kind() == Error && element.as_token().is_some();
            let starts_group = error && !previous_error;
            previous_error = error;
            starts_group
        })
        .count();
    assert_eq!(error_groups, 1);
    assert_eq!(
        root.descendants_with_tokens()
            .filter(|element| element.kind() == Error)
            .count(),
        1
    );
    assert!(!root.descendants().any(|node| matches!(
        node.kind(),
        SyntaxKind::Missing | SyntaxKind::Invalid | SyntaxKind::StructFieldForeignClose
    )));
}

#[test]
fn struct_field_separator_and_close_errors_are_distinct_without_error_spelling() {
    use crate::recovery_record::{
        ConstructRole, DeclarationRole, Delimiter, GrammarRole, RecoveryKind, StructRole,
    };
    use SyntaxKind::{Error, LBrace, Missing, RBrace, StructField};

    let separator = GrammarRole::Declaration(DeclarationRole::Struct(StructRole::FieldSeparator));
    let close = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::StructNamedFields,
        delimiter: Delimiter::Brace,
    };
    for (left, right, error_start, error_count, initial, eof, left_errors, right_errors) in [
        (
            "struct S{x:T;}",
            "struct S{x:T]}",
            12,
            1,
            false,
            false,
            vec![(separator, 12..13)],
            vec![(close, 12..13)],
        ),
        (
            "struct S{x:T;",
            "struct S{x:T]",
            12,
            1,
            false,
            true,
            vec![(separator, 12..13)],
            vec![(close, 12..13)],
        ),
        (
            "struct S{x:T;;}",
            "struct S{x:T;]}",
            12,
            2,
            false,
            false,
            vec![(separator, 12..14)],
            vec![(separator, 12..13), (close, 13..14)],
        ),
        (
            "struct S{;x:T}",
            "struct S{]x:T}",
            9,
            1,
            true,
            false,
            vec![(separator, 9..10)],
            vec![(close, 9..10)],
        ),
    ] {
        let mut projections = Vec::new();
        for (source, expected_errors) in [(left, left_errors), (right, right_errors)] {
            let (green, exit, records, remainder) =
                typed_struct_continuation(source, 0, None, 0, None);
            assert_eq!(green.to_string(), source);
            assert!(matches!(
                exit,
                NormalizedExit::Complete(Err(Either::Right(_)), _)
            ));
            assert_eq!(remainder, "");
            let node = declaration(&green);
            let mut expected = vec![(LBrace, false, 8..9)];
            if !initial {
                expected.push((StructField, true, 9..12));
            }
            expected.extend((error_start..error_start + error_count).map(|at| {
                if expected_errors
                    .iter()
                    .any(|(role, range)| *role == close && range.start == at)
                {
                    (SyntaxKind::StructFieldForeignClose, true, at..at + 1)
                } else {
                    (Error, false, at..at + 1)
                }
            }));
            if initial {
                expected.push((StructField, true, 10..13));
            }
            expected.push(if eof {
                (Missing, true, source.len()..source.len())
            } else {
                (RBrace, false, source.len() - 1..source.len())
            });
            assert_eq!(
                node.children_with_tokens()
                    .skip_while(|element| element.kind() != LBrace)
                    .map(|element| (
                        element.kind(),
                        element.as_node().is_some(),
                        usize::from(element.text_range().start())
                            ..usize::from(element.text_range().end()),
                    ))
                    .collect::<Vec<_>>(),
                expected,
                "{source:?}"
            );
            projections.push(cst_with_opaque_error_spelling(&SyntaxNode::new_root(green)));

            // Temporary records are counterexample evidence of different roles and
            // group partitions, never input to the future CST slot interpreter.
            let mut expected_records = expected_errors
                .into_iter()
                .map(|(role, range)| (RecoveryKind::Error, role, range))
                .collect::<Vec<_>>();
            if eof {
                expected_records.push((RecoveryKind::Missing, close, source.len()..source.len()));
            }
            assert_eq!(
                records
                    .into_iter()
                    .map(|record| (record.kind, record.site.role, record.site.range))
                    .collect::<Vec<_>>(),
                expected_records,
                "{source:?}"
            );
        }
        assert_ne!(projections[0], projections[1], "{left:?} versus {right:?}");
    }
}

#[test]
fn struct_field_foreign_close_wraps_one_maximal_run_with_unchanged_records() {
    use crate::recovery_record::{GrammarRole, RecoveryKind};
    for (source, runs) in [
        ("struct S{]x:T}", vec!["]"]),
        ("struct S{x:T,]y:U}", vec!["]"]),
        ("struct S{x:T]}", vec!["]"]),
        ("struct S{x:T;]}", vec!["]"]),
        ("struct S{x:T];}", vec!["]"]),
        ("struct S{x:T] )}", vec!["] )"]),
        ("struct S{],x:T]}", vec!["]", "]"]),
        ("struct S(]T)", vec!["]"]),
        ("struct S(T,]U)", vec!["]"]),
        ("struct S(T];)", vec!["]"]),
        ("struct S(T] }", vec!["] }"]),
        ("struct S{ \t] /*名*/ ) \r\n x:T}", vec!["] /*名*/ )"]),
    ] {
        let origin = 100;
        let (green, _, records) = typed_struct(source, origin, None, 0, None);
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green.clone());
        let wrappers = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::StructFieldForeignClose)
            .collect::<Vec<_>>();
        assert_eq!(
            wrappers.iter().map(ToString::to_string).collect::<Vec<_>>(),
            runs,
            "{source:?}"
        );
        let close_records = records
            .iter()
            .filter(|record| {
                record.kind == RecoveryKind::Error
                    && matches!(record.site.role, GrammarRole::ClosingDelimiter { .. })
            })
            .collect::<Vec<_>>();
        assert_eq!(wrappers.len(), close_records.len());
        for (wrapper, record) in wrappers.iter().zip(close_records) {
            assert_eq!(
                wrapper.parent().unwrap().kind(),
                SyntaxKind::StructDeclaration
            );
            assert!(
                wrapper
                    .children_with_tokens()
                    .all(|child| child.as_token().is_some() && child.kind() == SyntaxKind::Error)
            );
            assert_eq!(
                record.site.range,
                origin + usize::from(wrapper.text_range().start())
                    ..origin + usize::from(wrapper.text_range().end())
            );
        }
        let (frozen, _, replayed) = typed_struct(source, origin, Some(&records), 0, None);
        assert_eq!(frozen, green);
        assert_eq!(replayed, records);
    }
}

#[test]
fn struct_field_foreign_close_is_absent_from_other_field_recovery() {
    for source in [
        "struct S{x:T,y:U}",
        "struct S(T,U)",
        "struct S{x:T;}",
        "struct S{",
        "struct S(T",
        "struct S{x:=T}",
        "struct S:\n  x:T;\n  y:U",
        "enum E{V{x:T]}",
        "enum E{V(T]}",
        "error E{V{x:T]}",
        "error E{V(T]}",
    ] {
        let (green, _) = run_statement(source);
        let root = SyntaxNode::new_root(green);
        if source.starts_with("struct S:") {
            let fields = root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::StructField)
                .collect::<Vec<_>>();
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].to_string(), "x:T");
            assert_eq!(fields[1].to_string(), "y:U");
            for field in fields {
                assert_eq!(
                    field.parent().unwrap().kind(),
                    SyntaxKind::StructDeclaration
                );
            }
        }
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::StructFieldForeignClose),
            "{source:?}"
        );
    }
}

#[test]
fn struct_field_foreign_close_finishes_before_active_stop_leading() {
    let source = "struct S(T] \r\n : next";
    let (green, exit, _, remainder) =
        typed_struct_continuation(source, 100, None, crate::lexical::stops::STOP_COLON, None);
    assert_eq!(green.to_string(), "struct S(T]");
    assert_eq!(remainder, " next");
    let NormalizedExit::Complete(Err(Either::Left(mut item)), _) = exit else {
        panic!("active stop must stay pending")
    };
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Colon));
    assert_eq!(emit_pending_leading_text(&mut item), " \r\n ");
    let node = declaration(&green);
    let wrapper = node
        .children()
        .find(|node| node.kind() == SyntaxKind::StructFieldForeignClose)
        .unwrap();
    assert_eq!(wrapper.to_string(), "]");
    assert_eq!(wrapper.next_sibling().unwrap().kind(), SyntaxKind::Missing);
}

#[test]
fn struct_field_foreign_close_finishes_at_protected_fence() {
    use crate::lexical::item::{BorrowedTarget, Boundary};
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    use crate::recovery_record::{ConstructRole, Delimiter, GrammarRole, RecoveryKind};

    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let origin = 100;
    let accepted = "struct S{] /*名*/ )";
    let source = format!("{accepted}\r\n>> ```\r\nouter");
    let (green, exit, records, remainder) =
        typed_struct_continuation(&source, origin, None, 0, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, ">> ```\r\nouter");
    let node = declaration(&green);
    let wrappers = node
        .children()
        .filter(|node| node.kind() == SyntaxKind::StructFieldForeignClose)
        .collect::<Vec<_>>();
    assert_eq!(wrappers.len(), 1);
    let wrapper = &wrappers[0];
    assert_eq!(wrapper.to_string(), "] /*名*/ )");
    assert_eq!(usize::from(wrapper.text_range().start()), 9);
    assert_eq!(usize::from(wrapper.text_range().end()), accepted.len());
    assert!(
        wrapper
            .children_with_tokens()
            .all(|child| child.as_token().is_some() && child.kind() == SyntaxKind::Error)
    );
    assert_eq!(wrapper.next_sibling().unwrap().kind(), SyntaxKind::Missing);
    assert_eq!(records.len(), 2);
    assert_eq!(records[0].kind, RecoveryKind::Error);
    assert_eq!(records[0].site.range, origin + 9..origin + accepted.len());
    assert_eq!(
        records[0].site.role,
        GrammarRole::ClosingDelimiter {
            owner: ConstructRole::StructNamedFields,
            delimiter: Delimiter::Brace,
        }
    );
    assert_eq!(records[1].kind, RecoveryKind::Missing);
    let (again, frozen_exit, frozen, frozen_remainder) =
        typed_struct_continuation(&source, origin, Some(&records), 0, Some(&fence));
    assert_eq!(again, green);
    assert_eq!(frozen, records);
    assert_eq!(frozen_remainder, remainder);
    for exit in [exit, frozen_exit] {
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("foreign-close recovery must return the protected fence")
        };
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, "\r\n");
        assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
        assert!(matches!(
            pending.into_kind(),
            Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
        ));
    }
}

fn cst_with_opaque_error_spelling(node: &SyntaxNode) -> String {
    node.preorder_with_tokens()
        .map(|event| {
            let (enter, element) = match event {
                rowan::WalkEvent::Enter(element) => (true, element),
                rowan::WalkEvent::Leave(element) => (false, element),
            };
            // Retain nesting, node/token identity, kinds, ranges and native text.
            // Do not read Error spelling, including through an enclosing node.
            let text = element.as_token().map(|token| {
                if token.kind() == SyntaxKind::Error {
                    "<opaque>"
                } else {
                    token.text()
                }
            });
            format!(
                "{enter:?} {:?} {:?} {:?} {text:?}\n",
                element.kind(),
                element.as_node().is_some(),
                element.text_range(),
            )
        })
        .collect()
}

#[test]
fn struct_field_separator_error_keeps_active_stop_leading_pending() {
    use SyntaxKind::{Error, Missing, StructField};
    let source = "struct S(T; : next";
    let operators = OperatorTable::empty();
    let (green, exit) =
        run_statement_with_stops(source, &operators, crate::lexical::stops::STOP_COLON);
    assert_eq!(green.to_string(), "struct S(T;");
    let Some(Err(Either::Left(mut item))) = exit else {
        panic!("active stop must remain pending")
    };
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Colon));
    assert_eq!(emit_pending_leading_text(&mut item), " ");
    let root = SyntaxNode::new_root(green);
    let sequence = root
        .descendants()
        .find(|node| node.kind() == StructField)
        .unwrap()
        .parent()
        .unwrap();
    assert_eq!(sequence.kind(), SyntaxKind::StructDeclaration);
    let tail = sequence
        .children_with_tokens()
        .skip_while(|element| element.kind() != StructField)
        .collect::<Vec<_>>();
    assert_eq!(
        tail.iter()
            .map(|element| (
                element.kind(),
                usize::from(element.text_range().start())..usize::from(element.text_range().end()),
                element.to_string()
            ))
            .collect::<Vec<_>>(),
        [
            (StructField, 9..10, "T".to_owned()),
            (Error, 10..11, ";".to_owned()),
            (Missing, 11..11, "".to_owned())
        ]
    );
    assert!(tail[1].as_token().is_some());
    assert_field_item_children(tail[2].as_node().unwrap(), 11, &[]);
    // The only Missing is the independently required local close after handoff.
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == Missing)
            .count(),
        1
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter(|element| element.kind() == Error)
            .count(),
        1
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Invalid)
    );
}

pub(super) fn assert_empty_field_list_close_missing_cst(
    prefix: &str,
    suffix: &str,
    ancestors: &[SyntaxKind],
) {
    use SyntaxKind::{Error, Invalid, LBrace, LParen, Missing, RBrace, RParen, StructField};
    let (open, close) = if prefix.ends_with('{') {
        (LBrace, RBrace)
    } else {
        (LParen, RParen)
    };
    for closed in [false, true] {
        let source = format!("{prefix}{}", if closed { suffix } else { "" });
        let (green, exit) = run_statement(&source);
        assert_eq!(green.to_string(), source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        let sequence = root
            .descendants()
            .find(|node| node.kind() == ancestors[0])
            .unwrap();
        assert_eq!(
            sequence
                .ancestors()
                .take(ancestors.len())
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            ancestors
        );
        let p = prefix.len();
        assert_eq!(
            sequence
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
                (open, false, p - 1..p, prefix[p - 1..].to_owned()),
                if closed {
                    (close, false, p..p + 1, suffix[..1].to_owned())
                } else {
                    (Missing, true, p..p, String::new())
                },
            ],
            "{source:?}\n{root:#?}"
        );
        let missing = root
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect::<Vec<_>>();
        assert_eq!(missing.len(), if closed { 0 } else { ancestors.len() });
        if !closed {
            assert_eq!(missing[0].parent().as_ref(), Some(&sequence));
            if ancestors.len() == 2 {
                let declaration = sequence.parent().unwrap();
                assert_eq!(missing[1].parent().as_ref(), Some(&declaration));
                assert_eq!(sequence.next_sibling().as_ref(), Some(&missing[1]));
                assert!(missing[1].next_sibling_or_token().is_none());
            }
            for node in missing {
                assert_field_item_children(&node, p, &[]);
            }
        }
        assert!(root.descendants_with_tokens().all(|element| !matches!(
            element.kind(),
            StructField | Error | Invalid | SyntaxKind::StructFieldForeignClose
        )));
    }
}

#[test]
fn struct_empty_field_list_close_missing_has_direct_cst_slot() {
    for (prefix, suffix) in [("struct S{", "}"), ("struct S(", ")")] {
        assert_empty_field_list_close_missing_cst(prefix, suffix, &[SyntaxKind::StructDeclaration]);
    }
}

#[test]
fn struct_field_local_close_missing_preserves_active_stop_cst() {
    let (green, exit, _, remainder) = typed_struct_continuation(
        "struct S(T \r\n : next",
        100,
        None,
        crate::lexical::stops::STOP_COLON,
        None,
    );
    assert_eq!(green.to_string(), "struct S(T");
    assert_eq!(remainder, " next");
    let NormalizedExit::Complete(Err(Either::Left(mut item)), _) = exit else {
        panic!("active stop must stay pending")
    };
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Colon));
    assert_eq!(emit_pending_leading_text(&mut item), " \r\n ");
    assert_struct_local_close_missing_tail(&green, true);
}

#[test]
fn struct_field_local_close_missing_preserves_protected_fence_cst() {
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
    let (green, exit, _, remainder) =
        typed_struct_continuation("struct S(\r\n>> ```\r\nouter", 100, None, 0, Some(&fence));
    assert_eq!(green.to_string(), "struct S(");
    assert_eq!(remainder, ">> ```\r\nouter");
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart) = exit else {
        panic!("fence must stay pending at physical line start")
    };
    let (leading, pending) = emit_terminal_leading_text(item);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), 111);
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));
    assert_struct_local_close_missing_tail(&green, false);
}

fn assert_struct_local_close_missing_tail(green: &GreenNode, has_field: bool) {
    use SyntaxKind::{Error, Invalid, LParen, Missing, StructField, StructFieldForeignClose};
    let root = SyntaxNode::new_root(green.clone());
    let node = declaration(green);
    assert_eq!(node.kind(), SyntaxKind::StructDeclaration);
    assert_eq!(
        node.ancestors().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::StructDeclaration,
            SyntaxKind::Statement,
            SyntaxKind::Root,
        ]
    );
    let mut expected = vec![(LParen, false, 8..9, "(".to_owned())];
    if has_field {
        expected.push((StructField, true, 9..10, "T".to_owned()));
    }
    let at = if has_field { 10 } else { 9 };
    expected.push((Missing, true, at..at, String::new()));
    assert_eq!(
        node.children_with_tokens()
            .skip_while(|element| element.kind() != LParen)
            .map(|element| (
                element.kind(),
                element.as_node().is_some(),
                usize::from(element.text_range().start())..usize::from(element.text_range().end()),
                element.to_string(),
            ))
            .collect::<Vec<_>>(),
        expected
    );
    let missing = root
        .descendants()
        .filter(|node| node.kind() == Missing)
        .collect::<Vec<_>>();
    assert_eq!(missing.len(), 1);
    assert_eq!(
        missing[0].parent().unwrap().kind(),
        SyntaxKind::StructDeclaration
    );
    assert_field_item_children(&missing[0], at, &[]);
    assert_eq!(count(&root, StructField), usize::from(has_field));
    assert!(
        root.descendants_with_tokens()
            .all(|element| !matches!(element.kind(), Error | Invalid | StructFieldForeignClose))
    );
}

pub(super) fn assert_fresh_tuple_field_items_cst(
    prefix: &str,
    suffix: &str,
    ancestors: &[SyntaxKind],
) {
    use SyntaxKind::{Comma, Error, LParen, Missing, RParen, StructField, TypeExpression};
    for (body, closed, field_texts, fresh_index) in [
        (",T", true, vec!["", "T"], Some(0)),
        ("T,", false, vec!["T", ""], Some(1)),
        ("T,", true, vec!["T"], None),
        ("=T", true, vec!["=T"], None),
        ("T U", true, vec!["T U"], None),
    ] {
        let source = format!("{prefix}{body}{}", if closed { suffix } else { "" });
        let (green, exit) = run_statement(&source);
        assert_eq!(green.to_string(), source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        let fields = root
            .descendants()
            .filter(|node| node.kind() == StructField)
            .collect::<Vec<_>>();
        assert_eq!(fields.len(), field_texts.len(), "{source:?}\n{root:#?}");
        let sequence = fields[0].parent().unwrap();
        for (field, text) in fields.iter().zip(field_texts) {
            assert_eq!(field.to_string(), text);
            assert_eq!(field.parent().as_ref(), Some(&sequence));
            assert_eq!(
                field
                    .ancestors()
                    .skip(1)
                    .take(ancestors.len())
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                ancestors
            );
        }
        let mut children = vec![(LParen, "(")];
        match body {
            ",T" => children.extend([(StructField, ""), (Comma, ","), (StructField, "T")]),
            "T," => {
                children.extend([(StructField, "T"), (Comma, ",")]);
                if !closed {
                    children.push((StructField, ""));
                }
            }
            _ => children.push((StructField, body)),
        }
        children.push(if closed { (RParen, ")") } else { (Missing, "") });
        let mut offset = prefix.len() - 1;
        let expected = children
            .into_iter()
            .map(|(kind, text)| {
                let range = offset..offset + text.len();
                offset = range.end;
                (kind, range, text.to_owned())
            })
            .collect::<Vec<_>>();
        assert_eq!(
            sequence
                .children_with_tokens()
                .skip_while(|element| element.kind() != LParen)
                .map(|element| (
                    element.kind(),
                    usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end()),
                    element.to_string()
                ))
                .collect::<Vec<_>>(),
            expected,
            "{source:?}\n{root:#?}"
        );
        if let Some(index) = fresh_index {
            let at = if index == 0 {
                prefix.len()
            } else {
                source.len()
            };
            assert_field_item_children(&fields[index], at, &[(TypeExpression, "")]);
            let ty = fields[index].first_child().unwrap();
            assert_field_item_children(&ty, at, &[(Missing, "")]);
        }
        if body == "=T" {
            assert_field_item_children(
                &fields[0],
                prefix.len(),
                &[(Error, "="), (TypeExpression, "T")],
            );
        }
        if body == "T U" {
            assert_eq!(
                fields[0]
                    .children()
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                [TypeExpression]
            );
            assert_eq!(
                fields[0]
                    .descendants()
                    .filter(|node| node.kind() == SyntaxKind::TypeApplyArgument)
                    .count(),
                1
            );
        }
        if !closed {
            let missing = root
                .descendants()
                .filter(|node| node.kind() == Missing)
                .collect::<Vec<_>>();
            assert_eq!(missing.len(), 1 + ancestors.len());
            let fresh_type = fields[1].first_child().unwrap();
            assert_eq!(missing[0].parent().as_ref(), Some(&fresh_type));
            assert_eq!(missing[1].parent().as_ref(), Some(&sequence));
            assert_eq!(fields[1].next_sibling().as_ref(), Some(&missing[1]));
            if ancestors.len() == 2 {
                assert_eq!(missing[2].parent(), sequence.parent());
                assert_eq!(sequence.next_sibling().as_ref(), Some(&missing[2]));
            }
            for missing in root.descendants().filter(|node| node.kind() == Missing) {
                assert_field_item_children(&missing, source.len(), &[]);
            }
            if sequence.kind() == SyntaxKind::EnumVariant {
                let declaration = sequence.parent().unwrap();
                let tail = declaration
                    .children_with_tokens()
                    .skip_while(|element| element.as_node() != Some(&sequence))
                    .collect::<Vec<_>>();
                assert_eq!(tail.len(), 2);
                assert_eq!(tail[1].kind(), Missing);
            }
        }
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == Missing)
                .count(),
            usize::from(fresh_index.is_some()) + if closed { 0 } else { ancestors.len() }
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|element| element.kind() == Error)
                .count(),
            usize::from(body == "=T")
        );
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Invalid)
        );
    }
}

#[test]
fn struct_fresh_tuple_field_items_have_direct_cst_slots() {
    assert_fresh_tuple_field_items_cst("struct S(", ")", &[SyntaxKind::StructDeclaration]);
}

pub(super) fn assert_fresh_named_field_items_cst(
    prefix: &str,
    suffix: &str,
    ancestors: &[SyntaxKind],
) {
    use SyntaxKind::{Colon, Error, Identifier, Missing, StructField, TypeExpression, Whitespace};
    for (body, fresh_kind, fresh_text, between) in [
        (",x:T", Missing, "", vec![(SyntaxKind::Comma, ",")]),
        ("@ x:T", Error, "@", vec![(Whitespace, " "), (Missing, "")]),
    ] {
        let source = format!("{prefix}{body}{suffix}");
        let (green, exit) = run_statement(&source);
        assert_eq!(green.to_string(), source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        let fields = root
            .descendants()
            .filter(|node| node.kind() == StructField)
            .collect::<Vec<_>>();
        assert_eq!(fields.len(), 2, "{source:?}\n{root:#?}");
        for field in &fields {
            assert_eq!(
                field
                    .ancestors()
                    .skip(1)
                    .take(ancestors.len())
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                ancestors
            );
        }
        let start = prefix.len();
        assert_field_item_children(&fields[0], start, &[(fresh_kind, fresh_text)]);
        assert_field_item_children(
            &fields[1],
            start + body.len() - 3,
            &[(Identifier, "x"), (Colon, ":"), (TypeExpression, "T")],
        );
        assert_eq!(fields[0].parent(), fields[1].parent());
        let sequence = fields[0].parent().unwrap();
        let mut offset = start;
        let expected = std::iter::once((StructField, fresh_text))
            .chain(between)
            .chain(std::iter::once((StructField, "x:T")))
            .map(|(kind, text)| {
                let range = offset..offset + text.len();
                offset = range.end;
                (kind, range, text.to_owned())
            })
            .collect::<Vec<_>>();
        assert_eq!(
            sequence
                .children_with_tokens()
                .skip_while(|element| element.as_node() != Some(&fields[0]))
                .take(expected.len())
                .map(|element| (
                    element.kind(),
                    usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end()),
                    element.to_string()
                ))
                .collect::<Vec<_>>(),
            expected,
            "{source:?}\n{root:#?}"
        );
        assert!(
            root.descendants()
                .all(|node| node.kind() != SyntaxKind::Invalid)
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == Missing)
                .count(),
            1
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|element| element.kind() == Error)
                .count(),
            usize::from(fresh_kind == Error)
        );
    }
}

fn assert_field_item_children(field: &SyntaxNode, start: usize, children: &[(SyntaxKind, &str)]) {
    let mut offset = start;
    let expected = children
        .iter()
        .map(|&(kind, text)| {
            let range = offset..offset + text.len();
            offset = range.end;
            (kind, range, text.to_owned())
        })
        .collect::<Vec<_>>();
    assert_eq!(
        usize::from(field.text_range().start())..usize::from(field.text_range().end()),
        start..offset
    );
    assert_eq!(
        field
            .children_with_tokens()
            .map(|element| {
                if element.kind() == SyntaxKind::Error {
                    assert!(element.as_token().is_some());
                }
                if element.kind() == SyntaxKind::Missing {
                    assert_eq!(element.as_node().unwrap().children_with_tokens().count(), 0);
                }
                (
                    element.kind(),
                    usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end()),
                    element.to_string(),
                )
            })
            .collect::<Vec<_>>(),
        expected
    );
}

#[test]
fn struct_fresh_named_field_items_have_direct_cst_slots() {
    assert_fresh_named_field_items_cst("struct S{", "}", &[SyntaxKind::StructDeclaration]);
}

#[test]
fn struct_fresh_named_field_error_keeps_utf8_crlf_dedent_pending() {
    let prefix = "struct 名:\r\n  ";
    let accepted = format!("{prefix}@");
    let source = format!("{accepted}\r\n次");
    let (green, exit) = run_statement(&source);
    assert_eq!(green.to_string(), accepted);
    let Some(Err(Either::Left(mut item))) = exit else {
        panic!("dedented successor must remain pending")
    };
    assert_eq!(item.payload_view().spelling(), Some("次"));
    assert_eq!(emit_pending_leading_text(&mut item), "\r\n");
    let root = SyntaxNode::new_root(green);
    let fields = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::StructField)
        .collect::<Vec<_>>();
    assert_eq!(fields.len(), 1);
    assert_eq!(
        fields[0].parent().unwrap().kind(),
        SyntaxKind::StructDeclaration
    );
    assert_field_item_children(&fields[0], prefix.len(), &[(SyntaxKind::Error, "@")]);
    assert!(
        root.descendants()
            .all(|node| !matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Invalid))
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter(|element| element.kind() == SyntaxKind::Error)
            .count(),
        1
    );
}

// The same ordered head belongs to Struct, Enum, or Error through its ancestors.
pub(super) fn assert_named_field_head_cst(prefix: &str, suffix: &str, ancestors: &[SyntaxKind]) {
    use SyntaxKind::{Colon, Error, Identifier, Missing, TypeExpression, Whitespace};
    for (head, expected) in [
        (
            ": T",
            vec![
                (Missing, ""),
                (Colon, ":"),
                (Whitespace, " "),
                (TypeExpression, "T"),
            ],
        ),
        (
            "@ : T",
            vec![
                (Error, "@"),
                (Whitespace, " "),
                (Colon, ":"),
                (Whitespace, " "),
                (TypeExpression, "T"),
            ],
        ),
        (
            "x T",
            vec![
                (Identifier, "x"),
                (Whitespace, " "),
                (Missing, ""),
                (TypeExpression, "T"),
            ],
        ),
        (
            "x @ : T",
            vec![
                (Identifier, "x"),
                (Whitespace, " "),
                (Error, "@"),
                (Whitespace, " "),
                (Colon, ":"),
                (Whitespace, " "),
                (TypeExpression, "T"),
            ],
        ),
        (
            "x @ T",
            vec![
                (Identifier, "x"),
                (Whitespace, " "),
                (Error, "@"),
                (TypeExpression, " T"),
            ],
        ),
    ] {
        let source = format!("{prefix}{head}{suffix}");
        let (green, exit) = run_statement(&source);
        assert_eq!(green.to_string(), source);
        assert!(
            matches!(exit, Some(Err(Either::Right(_)))),
            "{source:?}: {exit:?}"
        );
        let root = SyntaxNode::new_root(green);
        let fields = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::StructField)
            .collect::<Vec<_>>();
        assert_eq!(fields.len(), 1, "{source:?}\n{root:#?}");
        let field = &fields[0];
        assert_eq!(field.text().to_string(), head, "{source:?}");
        assert_eq!(
            field
                .ancestors()
                .skip(1)
                .take(ancestors.len())
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            ancestors,
            "{source:?}"
        );
        let mut offset = prefix.len();
        let expected = expected
            .into_iter()
            .map(|(kind, text)| {
                let range = offset..offset + text.len();
                offset = range.end;
                (kind, range, text.to_owned())
            })
            .collect::<Vec<_>>();
        assert_eq!(offset, prefix.len() + head.len());
        assert_eq!(
            field
                .children_with_tokens()
                .map(|element| {
                    assert_eq!(element.parent(), Some(field.clone()));
                    if element.kind() == Error {
                        assert!(element.as_token().is_some());
                    }
                    if element.kind() == Missing {
                        assert!(element.as_node().is_some());
                    }
                    (
                        element.kind(),
                        usize::from(element.text_range().start())
                            ..usize::from(element.text_range().end()),
                        element.to_string(),
                    )
                })
                .collect::<Vec<_>>(),
            expected,
            "{source:?}\n{root:#?}"
        );
        assert!(
            root.descendants()
                .all(|node| node.kind() != SyntaxKind::Invalid)
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == Missing)
                .count(),
            usize::from(head == ": T" || head == "x T")
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|element| element.kind() == Error)
                .count(),
            usize::from(head.contains('@'))
        );
    }
}

#[test]
fn struct_named_field_head_has_direct_cst_slots_and_type_retry() {
    assert_named_field_head_cst("struct S{", "}", &[SyntaxKind::StructDeclaration]);
    assert_named_field_head_cst("struct 名:\r\n  ", "", &[SyntaxKind::StructDeclaration]);
}

#[test]
fn struct_named_field_colon_error_keeps_dedent_pending_without_missing() {
    let accepted = "struct S:\n  x @";
    let source = format!("{accepted}\r\nnext");
    let (green, exit) = run_statement(&source);
    assert_eq!(green.to_string(), accepted);
    let Some(Err(Either::Left(mut item))) = exit else {
        panic!("dedented successor must remain pending")
    };
    assert_eq!(item.payload_view().spelling(), Some("next"));
    assert_eq!(emit_pending_leading_text(&mut item), "\r\n");
    let root = SyntaxNode::new_root(green);
    let field = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::StructField)
        .unwrap();
    assert_eq!(
        field.parent().unwrap().kind(),
        SyntaxKind::StructDeclaration
    );
    assert_eq!(
        field
            .children_with_tokens()
            .map(|element| {
                assert_eq!(element.parent(), Some(field.clone()));
                if element.kind() == SyntaxKind::Error {
                    assert!(element.as_token().is_some());
                }
                (
                    element.kind(),
                    usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end()),
                    element.to_string(),
                )
            })
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Identifier, 12..13, "x".to_owned()),
            (SyntaxKind::Whitespace, 13..14, " ".to_owned()),
            (SyntaxKind::Error, 14..15, "@".to_owned()),
        ]
    );
    assert!(
        root.descendants()
            .all(|node| !matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Invalid))
    );
}

fn typed_struct(
    source: &str,
    origin: usize,
    frozen: Option<&[CommittedRecoveryRecord]>,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, NormalizedExit, Vec<CommittedRecoveryRecord>) {
    let (green, exit, records, _) = typed_struct_continuation(source, origin, frozen, stops, fence);
    (green, exit, records)
}

fn typed_struct_continuation<'a>(
    source: &'a str,
    origin: usize,
    frozen: Option<&[CommittedRecoveryRecord]>,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> (
    GreenNode,
    NormalizedExit,
    Vec<CommittedRecoveryRecord>,
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
    let exit = statement_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
        0,
        stops,
        origin,
        LineEntry::InLine,
        fence,
        Some(crate::ambient_claim::AmbientClaimView::root_statement(0)).into(),
        Some(crate::sequence::SequenceOwner::RootStatement),
    );
    builder.finish_node();
    let (green, records) = (builder.finish(), recover.finish_recoveries_for_test());
    (green, exit, records, input)
}

#[test]
fn struct_header_frozen_preserves_exact_close_and_newline_continuation() {
    for header in ["struct", "struct @", "struct S", "struct 名 @"] {
        for (leading, pending, suffix) in [
            ("  ", ")", "tail"),
            ("  ", "}", "tail"),
            ("  ", "]", "tail"),
            ("\r\n", "next", " tail"),
        ] {
            let source = format!("{header}{leading}{pending}{suffix}");
            let (green, exit, mut records, remainder) =
                typed_struct_continuation(&source, 100, None, 0, None);
            assert_eq!(green.to_string(), header);
            assert_eq!(records.len(), 1);
            assert_eq!(remainder, suffix);
            records[0].id = crate::recovery_record::DiagnosticId(71);
            let (again, frozen_exit, frozen, frozen_remainder) =
                typed_struct_continuation(&source, 100, Some(&records), 0, None);
            assert_eq!(again, green);
            assert_eq!(frozen, records);
            assert_eq!(frozen_remainder, remainder);
            let NormalizedExit::Complete(Err(Either::Left(mut item)), entry) = exit else {
                panic!("protected Item")
            };
            let NormalizedExit::Complete(Err(Either::Left(frozen_item)), frozen_entry) =
                frozen_exit
            else {
                panic!("frozen protected Item")
            };
            assert_eq!(frozen_item, item);
            assert_eq!(frozen_entry, entry);
            assert_eq!(entry, LineEntry::InLine);
            let successor_origin = 100 + source.len() - remainder.len();
            assert_eq!(
                successor_origin,
                100 + header.len() + leading.len() + pending.len()
            );
            assert_eq!(
                item.extent(successor_origin).payload(),
                100 + header.len() + leading.len()..successor_origin
            );
            assert_eq!(item.payload_view().spelling(), Some(pending));
            assert_eq!(emit_pending_leading_text(&mut item), leading);
        }
    }
}

#[test]
fn struct_header_visibility_rejection_preserves_seeded_output_and_cursor() {
    use crate::{
        cursor::recovery::RecoveryDraft,
        declaration::struct_decl::struct_declaration_selected_normalized,
        lexical::item::{LeadingTrivia, Payload, Token},
    };
    let (_, _, mut seed) = typed_struct("struct", 100, None, 0, None);
    seed[0].id = crate::recovery_record::DiagnosticId(71);
    for visibility in ["my", "our", "pub"] {
        for source in [" structure S;", "\r\nstruct S;"] {
            let operators = OperatorTable::empty();
            let mut recover = Recover::new_for_test(&operators);
            let mut input = source;
            let mut builder = {
                recover = Recover::reconcile_for_test(recover.operators(), &seed);
                GreenNodeBuilder::new()
            };
            builder.start_node(SyntaxKind::Root.into());
            builder.token(SyntaxKind::Identifier.into(), "seed");
            builder.start_node(SyntaxKind::Missing.into());
            builder.finish_node();
            recover.commit_recovery_for_test(RecoveryDraft::new(
                seed[0].site.clone(),
                seed[0].kind,
                seed[0].unexpected.clone(),
                seed[0].expectations.clone(),
                0,
            ));
            let before = recover.diagnostic_position();
            let make_item = || {
                Item::plain(
                    LeadingTrivia::default(),
                    Payload::Token(Token {
                        kind: TokenKind::Identifier,
                        text: visibility.into(),
                    }),
                )
            };
            let item = make_item();
            assert!(!struct_declaration_selected_normalized(
                crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
                &item,
                0,
                100,
                None
            ));
            assert_eq!(item, make_item());
            assert_eq!(input, source);
            assert_eq!(recover.diagnostic_position(), before);
            assert_eq!(recover.recovery_slot_count(), 1);
            builder.finish_node();
            let (green, records) = (builder.finish(), recover.finish_recoveries_for_test());
            assert_eq!(green.to_string(), "seed");
            assert_eq!(
                SyntaxNode::new_root(green).children_with_tokens().count(),
                2
            );
            assert_eq!(records, seed);
        }
    }
}

#[test]
fn struct_header_exact_shifted_frozen_records_and_native_runs() {
    use crate::recovery_record::{
        DeclarationRole, Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, StructRole, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    };
    use std::sync::Arc;
    for (source, slot, kind, range, text) in [
        (
            "struct",
            StructRole::Name,
            RecoveryKind::Missing,
            6..6,
            "struct",
        ),
        (
            "struct  ",
            StructRole::Name,
            RecoveryKind::Missing,
            8..8,
            "struct  ",
        ),
        (
            "struct;",
            StructRole::Name,
            RecoveryKind::Missing,
            6..6,
            "struct;",
        ),
        (
            "struct @ S;",
            StructRole::Name,
            RecoveryKind::Error,
            7..8,
            "struct @ S;",
        ),
        (
            "struct @ # S;",
            StructRole::Name,
            RecoveryKind::Error,
            7..10,
            "struct @ # S;",
        ),
        (
            "struct @  ",
            StructRole::Name,
            RecoveryKind::Error,
            7..8,
            "struct @",
        ),
        (
            "struct S",
            StructRole::BodyIntroducer,
            RecoveryKind::Missing,
            8..8,
            "struct S",
        ),
        (
            "struct S  ",
            StructRole::BodyIntroducer,
            RecoveryKind::Missing,
            10..10,
            "struct S  ",
        ),
        (
            "struct S Foo",
            StructRole::BodyIntroducer,
            RecoveryKind::Missing,
            8..8,
            "struct S ",
        ),
        (
            "struct S @ ;",
            StructRole::BodyIntroducer,
            RecoveryKind::Error,
            9..10,
            "struct S @ ;",
        ),
        (
            "struct S @  ",
            StructRole::BodyIntroducer,
            RecoveryKind::Error,
            9..10,
            "struct S @",
        ),
        (
            "struct 名 @ ;",
            StructRole::BodyIntroducer,
            RecoveryKind::Error,
            11..12,
            "struct 名 @ ;",
        ),
    ] {
        let (green, _, records) = typed_struct(source, 100, None, 0, None);
        assert_eq!(green.to_string(), text, "{source:?}");
        let range = range.start + 100..range.end + 100;
        let role = GrammarRole::Declaration(DeclarationRole::Struct(slot));
        let expected = if slot == StructRole::Name {
            vec![ExpectedSyntax::Identifier]
        } else {
            vec![
                ExpectedSyntax::Punctuation(PunctuationEvidence::Semicolon),
                ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace)),
                ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Parenthesis)),
                ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
            ]
        };
        assert_eq!(
            records,
            [CommittedRecoveryRecord {
                id: DiagnosticId(0),
                site: RecoverySiteKey {
                    role,
                    range: range.clone()
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
                expectations: expected
                    .into_iter()
                    .map(|expected| SyntaxExpectation {
                        role,
                        expected,
                        range: range.clone(),
                        sources: ExpectationSources::COMMITTED_RECOVERY_RULE
                    })
                    .collect::<Vec<_>>()
                    .into(),
                primary_expectation: 0
            }],
            "{source:?}"
        );
        let mut seeded = records.clone();
        seeded[0].id = DiagnosticId(71);
        let (again, _, frozen) = typed_struct(source, 100, Some(&seeded), 0, None);
        assert_eq!(again, green);
        assert_eq!(frozen, seeded);
    }
}

#[test]
fn struct_header_keeps_terminal_leading_and_accepts_deeper_retry() {
    for (source, text) in [
        ("struct  ]tail", "struct"),
        ("struct @  ]tail", "struct @"),
        ("struct S  ]tail", "struct S"),
        ("struct S @  ]tail", "struct S @"),
        ("struct\r\nnext", "struct"),
        ("struct @\r\nnext", "struct @"),
        ("struct S\r\nnext", "struct S"),
        ("struct S @\r\nnext", "struct S @"),
    ] {
        let (green, exit, records) = typed_struct(source, 100, None, 0, None);
        assert_eq!(green.to_string(), text, "{source:?}");
        assert_eq!(records.len(), 1);
        let NormalizedExit::Complete(Err(Either::Left(mut item)), _) = exit else {
            panic!("pending boundary")
        };
        assert!(emit_pending_leading_text(&mut item).len() >= 2);
    }
    for source in [
        "struct @\r\n  S;",
        "struct S @\r\n  ;",
        "struct @ S{}",
        "struct @ S()",
        "struct @ S:\n  x: F",
    ] {
        let (green, _, records) = typed_struct(source, 0, None, 0, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(records.len(), 1);
    }
}

fn declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::StructDeclaration)
        .expect("StructDeclaration")
}

#[test]
fn struct_header_active_starters_and_quoted_fences_remain_whole() {
    use crate::lexical::{
        stops::{STOP_COLON, STOP_LBRACE},
        yumark::{FenceOpener, FencePrefixPolicy},
    };
    use crate::recovery_record::RecoveryKind;
    for (source, text, stops, leading) in [
        ("struct  :tail", "struct", STOP_COLON, "  "),
        ("struct @  :tail", "struct @", STOP_COLON, "  "),
        ("struct S  :tail", "struct S", STOP_COLON, "  "),
        ("struct S @  :tail", "struct S @", STOP_COLON, "  "),
        ("struct  {tail", "struct", STOP_LBRACE, "  "),
        ("struct S @  {tail", "struct S @", STOP_LBRACE, "  "),
        ("struct\r\n", "struct", STOP_COLON, "\r\n"),
        ("struct S\r\n", "struct S", STOP_COLON, "\r\n"),
    ] {
        let (green, exit, records) = typed_struct(source, 100, None, stops, None);
        assert_eq!(green.to_string(), text, "{source:?}");
        assert_eq!(records.len(), 1);
        let mut item = match exit {
            NormalizedExit::Complete(Err(Either::Left(item)), _) => item,
            NormalizedExit::Complete(Err(Either::Right(end)), _) => end.item,
            _ => panic!("protected item"),
        };
        assert_eq!(emit_pending_leading_text(&mut item), leading);
        if !source.contains('@') {
            assert_eq!(records[0].site.range, 100 + text.len()..100 + text.len());
        }
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
    for (source, text, range, kind) in [
        (
            "struct\r\n>> ```",
            "struct",
            108..108,
            RecoveryKind::Missing,
        ),
        (
            "struct @\r\n>> ```",
            "struct @",
            107..108,
            RecoveryKind::Error,
        ),
        (
            "struct S\r\n>> ```",
            "struct S",
            110..110,
            RecoveryKind::Missing,
        ),
        (
            "struct S @\r\n>> ```",
            "struct S @",
            109..110,
            RecoveryKind::Error,
        ),
    ] {
        let (green, exit, records) = typed_struct(source, 100, None, 0, Some(&fence));
        assert_eq!(green.to_string(), text);
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].site.range, range);
        assert_eq!(records[0].kind, kind);
        assert!(
            matches!(exit, NormalizedExit::Complete(Err(Either::Left(ref item)), _) if item.payload_view().is_boundary())
        );
        let (again, _, frozen) = typed_struct(source, 100, Some(&records), 0, Some(&fence));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
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

fn assert_pending_word_with_leading(exit: Option<TailExit>, word: &str, leading: &str) {
    let mut item = match exit {
        Some(Err(Either::Left(item))) => item,
        Some(Err(Either::Right(end))) => end.item,
        _ => panic!("{word:?} must remain pending"),
    };
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    assert_eq!(item.payload_view().spelling(), Some(word));
    assert_eq!(emit_pending_leading_text(&mut item), leading);
}

#[test]
fn struct_c11_builds_exact_direct_topology_and_forms() {
    for (source, fields) in [
        ("struct Empty;", 0),
        ("my struct Point{x: F, y: Y}", 2),
        ("our struct Pair(F, G)", 2),
        ("pub struct Row:\n  x: F\n  y: Y", 2),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            node.parent().map(|node| node.kind()),
            Some(SyntaxKind::Statement)
        );
        assert_eq!(count(&node, SyntaxKind::StructField), fields, "{source:?}");
        assert_eq!(
            count(&node, SyntaxKind::TypeExpression),
            fields,
            "{source:?}"
        );
        assert_eq!(count(&node, SyntaxKind::BindingHeader), 0, "{source:?}");
    }
}

#[test]
fn struct_c11_dispatch_is_exact_and_irrevocable() {
    for source in [
        "struct S;",
        "my struct S;",
        "our struct S;",
        "pub struct S;",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        declaration(&green);
    }
    for source in ["structure", "structural", "my structure = value"] {
        let (green, _) = run_statement(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::StructDeclaration),
            "{source:?}"
        );
    }
    let (green, _) = run_statement("my struct = value");
    let root = SyntaxNode::new_root(green);
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::StructDeclaration)
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BindingStatement)
    );
}

#[test]
fn struct_c11_keeps_dynamic_word_operator_names_raw() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new("Dynamic", OperatorFixities::new().with_nullfix()),
        OperatorDeclaration::new("field", OperatorFixities::new().with_nullfix()),
    ])
    .expect("dynamic Struct-name operator table");
    let source = "struct Dynamic{field: T}";
    let (green, exit) = run_statement_with(source, &operators);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::NullfixOperatorUse), 0);
    assert_eq!(count(&node, SyntaxKind::Error), 0);
    assert_eq!(count(&node, SyntaxKind::StructField), 1);
}

#[test]
fn struct_c11_named_boundary_splits_only_complete_next_fields() {
    for (source, fields, types, missing) in [
        ("struct S{x:F y:Y}", 2, 2, 1),
        ("struct S{x:F Y}", 1, 2, 0),
        ("struct S{x:Pair(F Y)}", 1, 3, 0),
        ("struct S(F Y)", 1, 2, 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::StructField), fields, "{source:?}");
        assert_eq!(
            count(&node, SyntaxKind::TypeExpression),
            types,
            "{source:?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            missing,
            "{source:?}\n{node:#?}"
        );
    }
}

#[test]
fn struct_c11_gap_rules_keep_shallow_items_pending() {
    let (green, _) = run_statement("my\nstruct S;");
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::StructDeclaration)
    );

    let (green, exit) = run_statement("struct\nName;");
    assert_eq!(green.to_string(), "struct");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    for (source, fields, missing) in [
        ("struct S{x\n:y}", 2, 2),
        ("struct S{x\n  :y}", 2, 3),
        ("struct S{x:\nY}", 2, 2),
        ("struct S{x:\n  Y}", 1, 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::StructField), fields, "{source:?}");
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            missing,
            "{source:?}\n{node:#?}"
        );
    }
}

#[test]
fn struct_c11_header_and_body_recovery_stays_owner_local() {
    for (source, missing, errors) in [
        ("struct;", 1, 0),
        ("struct @ S;", 0, 1),
        ("struct S @ ;", 0, 1),
        ("struct S:", 1, 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::Missing), missing, "{source:?}");
        assert_eq!(count(&node, SyntaxKind::Error), errors, "{source:?}");
    }
}

#[test]
fn struct_c11_malformed_recovery_owns_trailing_eof_trivia() {
    for (source, error_parent, error_text) in [
        ("struct @ ", SyntaxKind::StructDeclaration, "@"),
        ("struct S @ ", SyntaxKind::StructDeclaration, "@"),
        ("struct S{x @ ", SyntaxKind::StructField, "@"),
        ("struct S{@ ", SyntaxKind::StructField, "@"),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let root = SyntaxNode::new_root(green);
        let trailing = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .last()
            .expect("trailing EOF trivia token");
        assert_eq!(trailing.kind(), SyntaxKind::Whitespace, "{source:?}");
        assert_eq!(trailing.text(), " ", "{source:?}");
        if error_parent == SyntaxKind::StructDeclaration {
            // Header Error leaves terminal EOF leading to the pending Item.
            assert_eq!(trailing.parent().unwrap().kind(), SyntaxKind::Root);
        }
        let error = crate::tests::recovery_output::recovery_groups(&root)
            .into_iter()
            .next()
            .unwrap();
        assert!(
            matches!(&error, crate::tests::recovery_output::RecoveryGroup::Raw(_)),
            "{source:?}"
        );
        assert_eq!(error.to_string(), error_text, "{source:?}");
        assert_eq!(
            error.parent().map(|node| node.kind()),
            Some(error_parent),
            "{source:?}",
        );
    }
}

#[test]
fn struct_named_field_records_are_exact_and_frozen() {
    use crate::recovery_record::{
        DeclarationRole, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, StructRole, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    };
    use std::sync::Arc;

    for (source, slot, kind, range, expected) in [
        (
            "struct S{: T}",
            StructRole::FieldName,
            RecoveryKind::Missing,
            9..9,
            ExpectedSyntax::Identifier,
        ),
        (
            "struct S{x T}",
            StructRole::FieldColon,
            RecoveryKind::Missing,
            11..11,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        ),
        (
            "struct S{@ : T}",
            StructRole::FieldName,
            RecoveryKind::Error,
            9..10,
            ExpectedSyntax::Identifier,
        ),
        (
            "struct S{x @ : T}",
            StructRole::FieldColon,
            RecoveryKind::Error,
            11..12,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        ),
    ] {
        let (green, _, records) = typed_struct(source, 100, None, 0, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        let range = range.start + 100..range.end + 100;
        let role = GrammarRole::Declaration(DeclarationRole::Struct(slot));
        assert_eq!(
            records,
            [CommittedRecoveryRecord {
                id: DiagnosticId(0),
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
                    range: range.clone(),
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }]),
                primary_expectation: 0,
            }],
            "{source:?}",
        );
        let mut seeded = records.clone();
        seeded[0].id = DiagnosticId(71);
        let (again, _, frozen) = typed_struct(source, 100, Some(&seeded), 0, None);
        assert_eq!(again, green, "{source:?}");
        assert_eq!(frozen, seeded, "{source:?}");
    }

    let (green, _, records) = typed_struct("struct S{@ x: T}", 100, None, 0, None);
    assert_eq!(green.to_string(), "struct S{@ x: T}");
    let field = GrammarRole::Declaration(DeclarationRole::Struct(StructRole::Field));
    let separator = GrammarRole::Declaration(DeclarationRole::Struct(StructRole::FieldSeparator));
    assert_eq!(
        records,
        [
            CommittedRecoveryRecord {
                id: DiagnosticId(0),
                site: RecoverySiteKey {
                    role: field,
                    range: 109..110
                },
                kind: RecoveryKind::Error,
                unexpected: Arc::from([UnexpectedSyntax::Token {
                    range: 109..110,
                    category: UnexpectedCategory::OtherCharacter,
                }]),
                expectations: Arc::from([SyntaxExpectation {
                    role: field,
                    expected: ExpectedSyntax::Identifier,
                    range: 109..110,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }]),
                primary_expectation: 0,
            },
            CommittedRecoveryRecord {
                id: DiagnosticId(1),
                site: RecoverySiteKey {
                    role: separator,
                    range: 111..111
                },
                kind: RecoveryKind::Missing,
                unexpected: Arc::from([]),
                expectations: Arc::from([SyntaxExpectation {
                    role: separator,
                    expected: ExpectedSyntax::DelimitedSequenceSeparator,
                    range: 111..111,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }]),
                primary_expectation: 0,
            },
        ]
    );
}

#[test]
fn struct_named_brace_post_comma_field_and_close_missing_have_ordered_cst_evidence() {
    use crate::recovery_record::{
        CommittedRecoveryRecord, ConstructRole, DeclarationRole, Delimiter, DiagnosticId,
        ExpectationSources, ExpectedSyntax, GrammarRole, PunctuationEvidence, RecoveryKind,
        RecoverySiteKey, StructRole, SyntaxExpectation,
    };
    use SyntaxKind::{
        Colon, Comma, Identifier, LBrace, Missing, RBrace, StructDeclaration, StructField,
        TypeExpression, Whitespace,
    };
    use std::sync::Arc;

    let field_role = GrammarRole::Declaration(DeclarationRole::Struct(StructRole::Field));
    let close_role = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::StructNamedFields,
        delimiter: Delimiter::Brace,
    };
    let missing_record = |id, role, expected, at| CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: at..at,
        },
        kind: RecoveryKind::Missing,
        unexpected: Arc::from([]),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected,
            range: at..at,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    };

    let suffix = |declaration: &SyntaxNode| {
        declaration
            .children_with_tokens()
            .skip_while(|element| element.kind() != LBrace)
            .map(|element| {
                (
                    element.kind(),
                    element.as_node().is_some(),
                    usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end()),
                    element.to_string(),
                )
            })
            .collect::<Vec<_>>()
    };
    for (source, field_range, missing_at, stops) in [
        ("struct S{x:T,", 13..13, 13, 0),
        ("struct S{x:T,  ", 13..15, 15, 0),
        (
            "struct S{x:T, ;tail",
            13..13,
            13,
            crate::lexical::stops::STOP_SEMICOLON,
        ),
    ] {
        let (green, exit, records, remainder) =
            typed_struct_continuation(source, 100, None, stops, None);
        assert_eq!(green.to_string(), &source[..missing_at], "{source:?}");
        if stops == 0 {
            assert!(matches!(
                exit,
                NormalizedExit::Complete(Err(Either::Right(_)), _)
            ));
            assert_eq!(remainder, "");
        } else {
            let NormalizedExit::Complete(Err(Either::Left(mut pending)), _) = exit else {
                panic!("semicolon must remain pending")
            };
            assert_eq!(
                pending.payload_view().token_kind(),
                Some(TokenKind::Semicolon)
            );
            assert_eq!(emit_pending_leading_text(&mut pending), " ");
            assert_eq!(remainder, "tail");
        }

        let root = SyntaxNode::new_root(green.clone());
        let declaration = root
            .descendants()
            .find(|node| node.kind() == StructDeclaration)
            .expect("StructDeclaration");
        let fields = declaration
            .children()
            .filter(|node| node.kind() == StructField)
            .collect::<Vec<_>>();
        assert_eq!(fields.len(), 2, "{source:?}");
        let accepted = &fields[0];
        assert_eq!(accepted.to_string(), "x:T");
        assert_eq!(
            accepted
                .children()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [TypeExpression]
        );
        assert_eq!(
            accepted
                .children_with_tokens()
                .map(|element| element.kind())
                .collect::<Vec<_>>(),
            [Identifier, Colon, TypeExpression]
        );
        assert!(
            !accepted.descendants().any(|node| node.kind() == Missing),
            "{source:?}"
        );

        let fresh = &fields[1];
        assert_eq!(
            fresh.text_range(),
            rowan::TextRange::new(field_range.start.into(), field_range.end.into())
        );
        assert_eq!(fresh.parent(), Some(declaration.clone()));
        assert_eq!(
            fresh
                .children_with_tokens()
                .map(|element| (element.kind(), element.to_string()))
                .collect::<Vec<_>>(),
            if missing_at == 13 {
                vec![(Missing, "".to_owned())]
            } else {
                vec![(Whitespace, "  ".to_owned()), (Missing, "".to_owned())]
            },
            "{source:?}"
        );
        let field_missing = fresh.last_child().expect("fresh field Missing");
        assert_eq!(field_missing.kind(), Missing);
        assert_eq!(usize::from(field_missing.text_range().start()), missing_at);
        assert_eq!(usize::from(field_missing.text_range().end()), missing_at);
        assert_eq!(field_missing.parent(), Some(fresh.clone()));
        let close_missing = fresh.next_sibling().expect("direct close Missing");
        assert_eq!(close_missing.kind(), Missing);
        assert_eq!(close_missing.parent(), Some(declaration.clone()));
        assert_eq!(close_missing.text_range(), field_missing.text_range());
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|element| element.kind() == Missing)
                .count(),
            2,
            "{source:?}"
        );
        for (missing, ancestry) in [
            (
                &field_missing,
                vec![
                    Missing,
                    StructField,
                    StructDeclaration,
                    SyntaxKind::Statement,
                    SyntaxKind::Root,
                ],
            ),
            (
                &close_missing,
                vec![
                    Missing,
                    StructDeclaration,
                    SyntaxKind::Statement,
                    SyntaxKind::Root,
                ],
            ),
        ] {
            assert_eq!(missing.children_with_tokens().count(), 0, "{source:?}");
            assert_eq!(
                missing
                    .ancestors()
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                ancestry,
                "{source:?}"
            );
        }
        assert_eq!(
            root.preorder_with_tokens()
                .filter_map(|event| match event {
                    rowan::WalkEvent::Enter(element)
                        if element.kind() == Missing
                            && element.text_range() == field_missing.text_range() =>
                    {
                        Some(element.parent().unwrap().kind())
                    }
                    _ => None,
                })
                .collect::<Vec<_>>(),
            [StructField, StructDeclaration],
            "{source:?}"
        );
        assert_eq!(
            suffix(&declaration),
            [
                (LBrace, false, 8..9, "{".to_owned()),
                (StructField, true, 9..12, "x:T".to_owned()),
                (Comma, false, 12..13, ",".to_owned()),
                (
                    StructField,
                    true,
                    field_range.start as usize..field_range.end as usize,
                    source[13..missing_at].to_owned()
                ),
                (Missing, true, missing_at..missing_at, "".to_owned()),
            ],
            "{source:?}"
        );
        assert!(
            !root.descendants_with_tokens().any(|node| matches!(
                node.kind(),
                SyntaxKind::Error | SyntaxKind::Invalid | SyntaxKind::StructFieldForeignClose
            )),
            "{source:?}"
        );

        let expected = vec![
            missing_record(0, field_role, ExpectedSyntax::Identifier, 100 + missing_at),
            missing_record(
                1,
                close_role,
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
                100 + missing_at,
            ),
        ];
        assert_eq!(records, expected, "{source:?}");
        let mut seeded = expected;
        seeded[0].id = DiagnosticId(71);
        let (again, _, frozen, frozen_remainder) =
            typed_struct_continuation(source, 100, Some(&seeded), stops, None);
        assert_eq!(again, green, "{source:?}");
        assert_eq!(frozen, seeded, "{source:?}");
        assert_eq!(frozen_remainder, remainder);
    }

    let accepted = "struct S{x:T,}";
    let (green, exit, records, remainder) = typed_struct_continuation(accepted, 0, None, 0, None);
    assert_eq!(green.to_string(), accepted);
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), _)
    ));
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let declaration = root
        .descendants()
        .find(|node| node.kind() == StructDeclaration)
        .expect("StructDeclaration");
    assert_eq!(
        suffix(&declaration),
        [
            (LBrace, false, 8..9, "{".to_owned()),
            (StructField, true, 9..12, "x:T".to_owned()),
            (Comma, false, 12..13, ",".to_owned()),
            (RBrace, false, 13..14, "}".to_owned()),
        ]
    );
    assert!(!root.descendants_with_tokens().any(|element| matches!(
        element.kind(),
        SyntaxKind::Error | SyntaxKind::Invalid | SyntaxKind::StructFieldForeignClose
    )));
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == StructField)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == Missing)
            .count(),
        0
    );
    assert!(records.is_empty());
}

#[test]
fn struct_named_field_runs_keep_per_item_facts_and_active_stops_pending() {
    use crate::{
        lexical::stops::STOP_COLON,
        recovery_record::{
            DeclarationRole, GrammarRole, StructRole, UnexpectedCategory, UnexpectedSyntax,
        },
    };

    let (green, _, records) = typed_struct("struct S{@ # : T}", 100, None, 0, None);
    assert_eq!(green.to_string(), "struct S{@ # : T}");
    assert_eq!(records.len(), 1);
    assert_eq!(
        records[0].site.role,
        GrammarRole::Declaration(DeclarationRole::Struct(StructRole::FieldName))
    );
    assert_eq!(records[0].site.range, 109..112);
    assert_eq!(
        records[0].unexpected,
        [
            UnexpectedSyntax::Token {
                range: 109..110,
                category: UnexpectedCategory::OtherCharacter,
            },
            UnexpectedSyntax::Token {
                range: 110..112,
                category: UnexpectedCategory::OtherCharacter,
            }
        ]
        .into()
    );

    for (source, stops, text, slot, pending) in [
        (
            "struct S{x : T}",
            STOP_COLON,
            "struct S{x ",
            StructRole::FieldColon,
            TokenKind::Colon,
        ),
        (
            "struct S{x @ : T}",
            STOP_COLON,
            "struct S{x @",
            StructRole::FieldColon,
            TokenKind::Colon,
        ),
    ] {
        let (green, exit, records) = typed_struct(source, 100, None, stops, None);
        assert_eq!(green.to_string(), text, "{source:?}");
        assert_eq!(records.len(), 2, "{source:?}");
        assert_eq!(
            records[0].site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(slot)),
            "{source:?}",
        );
        assert_eq!(
            records[1].site.role,
            GrammarRole::ClosingDelimiter {
                owner: crate::recovery_record::ConstructRole::StructNamedFields,
                delimiter: crate::recovery_record::Delimiter::Brace,
            },
            "{source:?}",
        );
        let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
            panic!("active field boundary must stay pending: {source:?}")
        };
        assert_eq!(
            item.payload_view().token_kind(),
            Some(pending),
            "{source:?}"
        );
    }
}

#[test]
fn struct_field_lists_publish_their_own_missing_and_mismatched_close() {
    use crate::recovery_record::{
        ConstructRole, Delimiter, ExpectedSyntax, GrammarRole, PunctuationEvidence, RecoveryKind,
    };

    for (source, owner, delimiter, kind, range) in [
        (
            "struct S{",
            ConstructRole::StructNamedFields,
            Delimiter::Brace,
            RecoveryKind::Missing,
            109..109,
        ),
        (
            "struct S(",
            ConstructRole::StructTupleFields,
            Delimiter::Parenthesis,
            RecoveryKind::Missing,
            109..109,
        ),
    ] {
        let (green, _, records) = typed_struct(source, 100, None, 0, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        let role = GrammarRole::ClosingDelimiter { owner, delimiter };
        assert_eq!(records.len(), 1, "{source:?}");
        assert_eq!(
            records[0].site,
            crate::recovery_record::RecoverySiteKey {
                role,
                range: range.clone()
            }
        );
        assert_eq!(records[0].kind, kind, "{source:?}");
        assert_eq!(
            records[0].expectations[0].expected,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter))
        );
        assert_eq!(
            records[0].unexpected.len(),
            usize::from(kind == RecoveryKind::Error)
        );
    }

    let (green, _, records) = typed_struct("struct S{)", 100, None, 0, None);
    assert_eq!(green.to_string(), "struct S{)");
    let role = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::StructNamedFields,
        delimiter: Delimiter::Brace,
    };
    assert_eq!(records.len(), 2);
    assert_eq!(records[0].site.role, role);
    assert_eq!(records[0].kind, RecoveryKind::Error);
    assert_eq!(records[0].site.range, 109..110);
    assert_eq!(records[1].site.role, role);
    assert_eq!(records[1].kind, RecoveryKind::Missing);
    assert_eq!(records[1].site.range, 110..110);
}

#[test]
fn struct_c11_gstruct_and_body_handoff_are_lossless() {
    for source in ["struct\n  Deep;", "struct Adjacent{}"] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        declaration(&green);
    }
    let (green, _) = run_statement("struct S Foo");
    let node = declaration(&green);
    assert_eq!(green.to_string(), "struct S ");
    assert_eq!(count(&node, SyntaxKind::StructField), 0);
    assert_eq!(count(&node, SyntaxKind::Missing), 1);

    let (green, exit) = run_statement("struct S 1");
    let node = declaration(&green);
    assert_eq!(green.to_string(), "struct S ");
    assert_eq!(count(&node, SyntaxKind::Missing), 1);
    assert_eq!(count(&node, SyntaxKind::Error), 0);
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    let (green, exit) = run_statement("struct S\nnext");
    assert_eq!(green.to_string(), "struct S");
    let Err(Either::Left(mut item)) = exit.expect("statement exit") else {
        panic!("pending item")
    };
    assert_eq!(emit_pending_leading_text(&mut item), "\n");

    let (green, exit) = run_statement("struct S:\nnext");
    assert_eq!(count(&declaration(&green), SyntaxKind::StructField), 1);
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
}

#[test]
fn struct_c11_body_colon_does_not_capture_polymorphic_variant_type() {
    let (green, exit) = run_statement("struct S :{A}");
    let node = declaration(&green);
    assert_eq!(green.to_string(), "struct S ");
    assert_eq!(count(&node, SyntaxKind::Missing), 1);
    assert_eq!(count(&node, SyntaxKind::Error), 0);
    let Some(Err(Either::Left(item))) = exit else {
        panic!("polymorphic variant type must remain pending")
    };
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::PolymorphicVariantColon)
    );
    assert_eq!(item.payload_view().spelling(), Some(":"));

    let source = "struct S:\n  x: T";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::StructField), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
}

#[test]
fn struct_c11_tuple_uses_the_complete_type_vocabulary() {
    let source = "struct S(for 'a: T, '[E], :{A}, [R])";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::StructField), 4);
    for kind in [
        SyntaxKind::ForallType,
        SyntaxKind::EffectRowType,
        SyntaxKind::PolymorphicVariantType,
        SyntaxKind::BracketRow,
    ] {
        assert_eq!(count(&node, kind), 1, "{kind:?}");
    }

    let source = "struct S(A; for 'a: T)";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::StructField), 2);
    assert_eq!(count(&node, SyntaxKind::ForallType), 1);

    let source = "struct S(,A,,)";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    let fields = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::StructField)
        .collect::<Vec<_>>();
    assert_eq!(fields.len(), 3);
    assert!(fields.iter().all(|field| {
        field
            .children()
            .all(|child| child.kind() == SyntaxKind::TypeExpression)
            && field
                .children()
                .any(|child| child.kind() == SyntaxKind::TypeExpression)
    }));
}

#[test]
fn struct_c11_trivia_stays_with_the_struct_sequence_and_named_gap() {
    let source = "struct S(\n  A, /*post*/\n  B\n)";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    let tuple_fields = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::StructField)
        .collect::<Vec<_>>();
    assert_eq!(tuple_fields.len(), 2);
    assert!(tuple_fields.iter().all(|field| {
        field
            .children()
            .map(|child| child.kind())
            .collect::<Vec<_>>()
            == [SyntaxKind::TypeExpression]
            && field
                .children_with_tokens()
                .all(|element| element.as_token().is_none())
    }));
    assert!(
        node.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| matches!(
                token.kind(),
                SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::BlockComment
            ))
            .all(|token| token.parent().as_ref() == Some(&node))
    );

    let source = "struct S{\n  x :  F,\n  y:Y\n}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    let first = node
        .children()
        .find(|child| child.kind() == SyntaxKind::StructField)
        .expect("named field");
    let ty = first
        .children()
        .find(|child| child.kind() == SyntaxKind::TypeExpression)
        .expect("field type");
    assert_eq!(ty.text().to_string(), "F");
    assert_eq!(first.text().to_string(), "x :  F");
}

#[test]
fn struct_c11_recovers_owned_fields_and_typed_closes() {
    for source in [
        "struct S{x F, y: Y}",
        "struct S{: F}",
        "struct S{x: , y:Y}",
        "struct S{x:F; y:Y}",
        "struct S{x:F; :Y}",
        "struct S(F; G)",
        "struct S{x:F] y:Y}",
        "struct S(F} G)",
        "struct S{x:F",
        "struct S(F",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        declaration(&green);
    }
}

#[test]
fn struct_c11_reaches_nested_canonical_consumers_but_not_inline_expr_slots() {
    for source in [
        "{struct S;}",
        "f:\n  struct S;",
        "if c:\n  struct S;",
        "case x:\n  p ->\n    struct S;",
        "catch x:\n  p ->\n    struct S;",
        "value with: struct S;",
        "value with:\n  struct S;",
        "mod M {struct S;}",
        "mod M:\n  struct S;",
        "mod M: struct S;",
        "my body =\n  struct S;",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        declaration(&green);
    }
    for source in [
        "f: struct S;",
        "if c: struct S;",
        "case x: p -> struct S;",
        "catch x: p -> struct S;",
        "my x = struct S;",
        "f struct S;",
    ] {
        let (green, _) = run(source);
        assert!(source.starts_with(&green.to_string()), "{source:?}");
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::StructDeclaration),
            "{source:?}"
        );
    }
}

#[test]
fn struct_attachment_schema_has_ordered_direct_occurrences() {
    use SyntaxKind::{
        Colon, DeclarationCompanion, DerivesClause, Identifier, LBrace, LParen, Newline, RBrace,
        RParen, Semicolon, StructField, StructKw, Whitespace,
    };

    let header = [(StructKw, 6), (Whitespace, 1), (Identifier, 1)];
    for (declaration_text, body, successor, leading, attached) in [
        ("struct S;", vec![(Semicolon, 1)], "with", " ", false),
        (
            "struct S{x:T}",
            vec![(LBrace, 1), (StructField, 3), (RBrace, 1)],
            "next",
            "  ",
            false,
        ),
        (
            "struct S(T)",
            vec![(LParen, 1), (StructField, 1), (RParen, 1)],
            "next",
            "  ",
            false,
        ),
        (
            "struct S:\n  x:T",
            vec![(Colon, 1), (Newline, 1), (Whitespace, 2), (StructField, 3)],
            "with",
            "\n",
            false,
        ),
        (
            "struct S derives Eq with {}",
            vec![(DerivesClause, 11), (DeclarationCompanion, 8)],
            "outer",
            " ",
            true,
        ),
        (
            "struct S{} derives Eq with {}",
            vec![
                (LBrace, 1),
                (RBrace, 1),
                (DerivesClause, 11),
                (DeclarationCompanion, 8),
            ],
            "outer",
            " ",
            true,
        ),
        (
            "struct S(T) derives Eq with {}",
            vec![
                (LParen, 1),
                (StructField, 1),
                (RParen, 1),
                (DerivesClause, 11),
                (DeclarationCompanion, 8),
            ],
            "outer",
            " ",
            true,
        ),
        (
            "struct S{x F} with {}",
            vec![
                (LBrace, 1),
                (StructField, 3),
                (RBrace, 1),
                (DeclarationCompanion, 8),
            ],
            "outer",
            " ",
            true,
        ),
        (
            "struct S(@) with {}",
            vec![
                (LParen, 1),
                (StructField, 1),
                (RParen, 1),
                (DeclarationCompanion, 8),
            ],
            "outer",
            " ",
            true,
        ),
        (
            "struct S{}",
            vec![(LBrace, 1), (RBrace, 1)],
            "with",
            "\r\n",
            false,
        ),
    ] {
        let tail = if successor == "with" { " {}" } else { " tail" };
        let source = format!("{declaration_text}{leading}{successor}{tail}");
        let origin = 8500;
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::InLine, None);
        let owner = assert_struct_attachment_shell(&green, declaration_text);
        let expected = header.into_iter().chain(body).collect::<Vec<_>>();
        assert_struct_attachment_children(&owner, 0, &expected, &source);
        if declaration_text == "struct S{x:T}" {
            let field = owner.children().find(|n| n.kind() == StructField).unwrap();
            assert_struct_attachment_children(
                &field,
                9,
                &[(Identifier, 1), (Colon, 1), (SyntaxKind::TypeExpression, 1)],
                &source,
            );
        }
        assert_eq!(
            owner
                .children()
                .filter(|n| n.kind() == DeclarationCompanion)
                .count(),
            usize::from(attached)
        );
        if attached {
            assert!(matches!(
                exit,
                NormalizedExit::Complete(Ok(()), LineEntry::InLine)
            ));
            assert_eq!(remainder, format!("{leading}{successor}{tail}"));
            let companion = owner
                .children()
                .find(|n| n.kind() == DeclarationCompanion)
                .unwrap();
            assert_struct_attachment_children(
                &companion,
                declaration_text.len() - 8,
                &[
                    (Whitespace, 1),
                    (SyntaxKind::WithKw, 4),
                    (Whitespace, 1),
                    (LBrace, 1),
                    (RBrace, 1),
                ],
                &source,
            );
        } else {
            let NormalizedExit::Complete(Err(Either::Left(mut pending)), entry) = exit else {
                panic!("closed or bodyless Struct must retain its successor: {source:?}")
            };
            assert_eq!(entry, LineEntry::InLine);
            assert_eq!(
                pending.payload_view().token_kind(),
                Some(TokenKind::Identifier)
            );
            assert_eq!(pending.payload_view().spelling(), Some(successor));
            assert_eq!(emit_pending_leading_text(&mut pending), leading);
            assert_eq!(remainder, tail);
            assert_eq!(
                origin + source.len() - remainder.len() - successor.len(),
                origin + declaration_text.len() + leading.len()
            );
        }
        // These recovery occurrences belong to the field/Type child, never to
        // the Struct header or companion attachment decision.
        assert_eq!(
            count(&owner, SyntaxKind::Missing),
            usize::from(declaration_text == "struct S{x F} with {}")
        );
        assert_eq!(
            count(&owner, SyntaxKind::Error),
            usize::from(declaration_text == "struct S(@) with {}")
        );
        for recovery in owner
            .descendants_with_tokens()
            .filter(|n| matches!(n.kind(), SyntaxKind::Missing | SyntaxKind::Error))
        {
            assert_ne!(recovery.parent(), Some(owner.clone()));
            if recovery.kind() == SyntaxKind::Missing {
                assert!(recovery.text_range().is_empty());
                assert!(
                    recovery
                        .as_node()
                        .unwrap()
                        .children_with_tokens()
                        .next()
                        .is_none()
                );
            } else {
                assert!(recovery.as_token().is_some());
            }
        }
    }
}

fn assert_struct_attachment_shell(green: &GreenNode, text: &str) -> SyntaxNode {
    let root = SyntaxNode::new_root(green.clone());
    assert_eq!(root.kind(), SyntaxKind::Root);
    assert_eq!(root.children_with_tokens().count(), 1);
    let statement = root.first_child().unwrap();
    assert_eq!(statement.kind(), SyntaxKind::Statement);
    assert_eq!(statement.parent(), Some(root));
    assert_eq!(statement.children_with_tokens().count(), 1);
    let owner = statement.first_child().unwrap();
    assert_eq!(owner.kind(), SyntaxKind::StructDeclaration);
    assert_eq!(owner.parent(), Some(statement));
    assert_eq!(owner.to_string(), text);
    assert_eq!(usize::from(owner.text_range().start()), 0);
    assert_eq!(usize::from(owner.text_range().end()), text.len());
    owner
}

fn assert_struct_attachment_children(
    owner: &SyntaxNode,
    start: usize,
    expected: &[(SyntaxKind, usize)],
    source: &str,
) {
    let children = owner.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children.len(), expected.len(), "{source:?}\n{owner:#?}");
    let mut at = start;
    for (child, &(kind, len)) in children.iter().zip(expected) {
        assert_eq!(child.parent().as_ref(), Some(owner));
        assert_eq!(child.kind(), kind, "{source:?}");
        assert_eq!(
            child.as_node().is_some(),
            matches!(
                kind,
                SyntaxKind::StructField
                    | SyntaxKind::TypeExpression
                    | SyntaxKind::DerivesClause
                    | SyntaxKind::DeclarationCompanion
            )
        );
        assert_eq!(
            usize::from(child.text_range().start())..usize::from(child.text_range().end()),
            at..at + len
        );
        assert_eq!(child.to_string(), source[at..at + len]);
        at += len;
    }
    assert_eq!(at, usize::from(owner.text_range().end()));
}

#[test]
fn struct_attachment_schema_caller_stop_wins_at_header_and_actual_close() {
    use SyntaxKind::{Identifier, LBrace, RBrace, StructKw, Whitespace};
    for (prefix, body) in [
        ("struct S", vec![]),
        ("struct S{}", vec![(LBrace, 1), (RBrace, 1)]),
    ] {
        let source = format!("{prefix} with {{}}");
        let (green, exit) = run_statement_with_stops(
            &source,
            &OperatorTable::empty(),
            crate::lexical::stops::STOP_WITH,
        );
        let owner = assert_struct_attachment_shell(&green, prefix);
        let expected = [(StructKw, 6), (Whitespace, 1), (Identifier, 1)]
            .into_iter()
            .chain(body)
            .collect::<Vec<_>>();
        assert_struct_attachment_children(&owner, 0, &expected, &source);
        assert_pending_word_with_leading(exit, "with", " ");
    }
}

#[test]
fn struct_attachment_schema_incomplete_lists_have_no_companion_occurrence() {
    for source in [
        "struct S{x:T with {}",
        "struct S{x:T] with ()",
        "struct S(A] with {}",
    ] {
        let (green, exit) = run_statement(source);
        let owner = assert_struct_attachment_shell(&green, source);
        assert_eq!(
            owner
                .children()
                .filter(|n| n.kind() == SyntaxKind::DeclarationCompanion)
                .count(),
            0
        );
        assert_eq!(count(&owner, SyntaxKind::DeclarationCompanion), 0);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
    }
}

#[test]
fn struct_companion_header_orders_derives_before_the_companion() {
    for (source, missing, errors) in [
        ("struct S with {}", 0, 0),
        ("struct S derives Eq with {}", 0, 0),
        ("struct S derives with {}", 1, 0),
        ("struct S derives @ with {}", 0, 1),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            1,
            "{source:?}"
        );
        assert_eq!(token_count(&node, SyntaxKind::WithKw), 1, "{source:?}");
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            missing,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::Error),
            errors,
            "{source:?}\n{node:#?}"
        );
        let owned = node
            .children()
            .filter(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::DerivesClause | SyntaxKind::DeclarationCompanion
                )
            })
            .map(|child| child.kind())
            .collect::<Vec<_>>();
        assert_eq!(
            owned.last(),
            Some(&SyntaxKind::DeclarationCompanion),
            "{source:?}: {owned:?}",
        );
    }
}

#[test]
fn struct_companion_trailing_follows_the_actual_matching_close() {
    for source in [
        "struct S{} derives Eq with {}",
        "struct S(A) derives Eq with {}",
        "struct S{x F} with {}",
        "struct S{x:F; y:Y} with {}",
        "struct S{x:F] y:Y} with {}",
        "struct S(@) with {}",
        "struct S(A; B) with {}",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            1,
            "{source:?}"
        );
    }

    for source in [
        "struct S{x:T with {}",
        "struct S{x:T] with ()",
        "struct S(A] with {}",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn struct_header_derives_hands_body_starters_back_by_role_phase() {
    for (source, fields) in [
        ("struct S derives {}", 0),
        ("struct S derives :\n  x:T", 1),
        ("struct S derives ;", 0),
        ("struct S derives Eq{}", 0),
        ("struct S derives Eq(A)", 1),
        ("struct S derives Eq:\n  x:T", 1),
        ("struct S derives Eq;", 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DerivesClause), 1, "{source:?}");
        assert_eq!(count(&node, SyntaxKind::StructField), fields, "{source:?}");
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 0);
    }

    for source in [
        "struct S derives (Eq) with {}",
        "struct S derives (Eq(A)) with {}",
        "struct S derives (Eq {x:T}) with {}",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DerivesClause), 1, "{source:?}");
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
        assert_eq!(count(&node, SyntaxKind::StructField), 0, "{source:?}");
    }

    let source = "struct S derives , with {}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::DerivesClause), 1);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 2);
}

#[test]
fn struct_companion_rejects_nontrailing_body_forms_and_incomplete_name() {
    for (source, leading) in [
        ("struct S; with {}", " "),
        ("struct S:\n  x:T\nwith {}", "\n"),
        ("struct ; with {}", " "),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}"
        );
        assert_pending_word_with_leading(exit, "with", leading);
    }

    let source = "struct S{x:T\nwith {}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert_eq!(
        count(&declaration(&green), SyntaxKind::DeclarationCompanion),
        0
    );
}

#[test]
fn struct_companion_suspends_with_inside_nested_derives_types() {
    let source = "struct S derives (A with B) with {}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
    assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
    assert!(
        node.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Identifier && token.text() == "with")
    );
}

#[test]
fn struct_companion_gap_and_contextual_word_judges_are_exact() {
    for source in ["struct S\n  with {}", "struct S\r\n  with {}"] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            1
        );
    }
    for (source, leading) in [
        ("struct S\nwith {}", "\n"),
        ("struct S{}\r\nwith {}", "\r\n"),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            0
        );
        assert_pending_word_with_leading(exit, "with", leading);
    }

    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "with",
        OperatorFixities::new().with_nullfix(),
    )])
    .expect("dynamic with operator table");
    let (green, exit) = run_statement_with("struct S{} with {}", &operators);
    assert_eq!(
        count(&declaration(&green), SyntaxKind::DeclarationCompanion),
        0
    );
    assert!(matches!(
        exit,
        Some(Err(Either::Left(_))) | Some(Err(Either::Right(_)))
    ));

    let (green, exit) = run_statement_with_stops(
        "struct S with {}",
        &OperatorTable::empty(),
        crate::lexical::stops::STOP_WITH,
    );
    assert_eq!(
        count(&declaration(&green), SyntaxKind::DeclarationCompanion),
        0
    );
    assert_pending_word_with_leading(exit, "with", " ");

    for source in ["struct S withx {}", "struct S within {}"] {
        let (green, _) = run_statement(source);
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn struct_companion_rejected_incomplete_lists_keep_the_exact_fence_handoff() {
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
    let origin = 8200;
    for accepted in [
        "> > struct S{x:T with {}",
        "> > struct S{x:T] with {}",
        "> > struct S(A with B",
        "> > struct S(A] with B",
    ] {
        let source = format!("{accepted}\r\n> > ```\r\nouter");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("the incomplete Struct body must return its exact fence boundary")
        };

        assert_eq!(green.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\r\nouter", "{accepted:?}");
        let node = declaration(&green);
        let wrappers = node
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::StructFieldForeignClose)
            .collect::<Vec<_>>();
        assert_eq!(wrappers.len(), usize::from(accepted.contains(']')));
        for wrapper in wrappers {
            assert_eq!(wrapper.to_string(), "]");
            assert_eq!(wrapper.parent().unwrap(), node);
        }
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            0,
            "{accepted:?}\n{node:#?}",
        );
        assert!(boundary.payload_view().is_boundary(), "{accepted:?}");
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, "\r\n", "{accepted:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + 2,
            "{accepted:?}",
        );
        assert!(matches!(
            pending.into_kind(),
            Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
        ));
    }
}

#[test]
fn struct_actual_close_returns_the_exact_normalized_successor() {
    let origin = 8300;
    for declaration_text in ["struct S{x:T}", "struct S(T)"] {
        let source = format!("{declaration_text}  next tail");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::InLine, None);
        let NormalizedExit::Complete(Err(Either::Left(mut successor)), LineEntry::InLine) = exit
        else {
            panic!("the closed Struct must return its exact successor")
        };

        assert_eq!(green.to_string(), declaration_text, "{declaration_text:?}");
        assert_eq!(remainder, " tail", "{declaration_text:?}");
        assert_eq!(
            successor.payload_view().token_kind(),
            Some(TokenKind::Identifier),
            "{declaration_text:?}",
        );
        assert_eq!(
            successor.payload_view().spelling(),
            Some("next"),
            "{declaration_text:?}",
        );
        assert_eq!(
            origin + source.len() - remainder.len() - "next".len(),
            origin + declaration_text.len() + 2,
            "{declaration_text:?}",
        );
        assert_eq!(
            emit_pending_leading_text(&mut successor),
            "  ",
            "{declaration_text:?}",
        );
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            0,
            "{declaration_text:?}",
        );
    }
}

#[test]
fn struct_accepted_companion_returns_the_exact_outer_remainder() {
    let origin = 8400;
    for declaration_text in ["struct S{} with {}", "struct S(T) with {}"] {
        let source = format!("{declaration_text} outer tail");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::InLine, None);
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Ok(()), LineEntry::InLine)
        ));

        assert_eq!(green.to_string(), declaration_text, "{declaration_text:?}");
        assert_eq!(remainder, " outer tail", "{declaration_text:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
        assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
    }
}

#[test]
fn struct_companion_streams_crlf_to_the_same_fence_boundary() {
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
    let origin = 8100;
    let accepted = "> > struct S{} derives Eq with: our x = y";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
    else {
        panic!("the Struct companion must return the exact fence boundary")
    };
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
    assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
}

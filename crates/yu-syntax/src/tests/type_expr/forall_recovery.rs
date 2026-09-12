use crate::tests::type_expr::record_field_recovery::field_record;
use crate::tests::type_expr::*;

fn forall_record(
    id: u32,
    role: TypeRole,
    range: Range<usize>,
    error: bool,
) -> CommittedRecoveryRecord {
    let expected = match role {
        TypeRole::ForallBinder => ExpectedSyntax::ForallTypeBinder,
        TypeRole::ForallBinderBoundary => ExpectedSyntax::TypeBinderBoundary,
        TypeRole::ForallColon => ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        TypeRole::ForallBody => ExpectedSyntax::TypeExpression,
        _ => panic!("only forall test records"),
    };
    let role = GrammarRole::Type(role);
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: if error {
            RecoveryKind::Error
        } else {
            RecoveryKind::Missing
        },
        unexpected: if error {
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

fn assert_typed_nodes(root: &SyntaxNode, expected: &[CommittedRecoveryRecord]) {
    for (syntax, recovery) in [
        (SyntaxKind::Missing, RecoveryKind::Missing),
        (SyntaxKind::Error, RecoveryKind::Error),
    ] {
        assert_eq!(
            if syntax == SyntaxKind::Error {
                recovery_groups(root).len()
            } else {
                root.descendants()
                    .filter(|node| node.kind() == syntax)
                    .count()
            },
            expected
                .iter()
                .filter(|record| record.kind == recovery)
                .count(),
            "{}",
            root.text(),
        );
    }
}

fn forall_cst(source: &str) -> SyntaxNode {
    let (green, _) = run_type(source);
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.text(), source, "{source:?}");
    root
}

fn direct_forall(root: &SyntaxNode) -> SyntaxNode {
    root.descendants()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type")
}

fn direct_kind_ranges(node: &SyntaxNode) -> Vec<(SyntaxKind, Range<usize>)> {
    node.children_with_tokens()
        .map(|child| {
            let range = child.text_range();
            (
                child.kind(),
                usize::from(range.start())..usize::from(range.end()),
            )
        })
        .collect()
}

#[test]
fn forall_head_composition_keeps_recovery_groups_in_their_direct_slots() {
    use SyntaxKind::*;

    // The same head loop composes first recovery, separator repetition and
    // recovered-Colon binder retries; extending the list never resets Colon.
    for suffix in [" @:@ T", "", " ", "\n"] {
        let source = format!("for @'a,;'b @'c{suffix}");
        let root = forall_cst(&source);
        let forall = direct_forall(&root);
        let mut expected = vec![
            (ForKw, 0..3),
            (ForallTypeBinder, 3..5),
            (ForallTypeBinder, 5..7),
            (ForallTypeBinder, 7..8),
            (ForallTypeBinder, 8..9),
            (ForallTypeBinder, 9..11),
            (Whitespace, 11..12),
            (Error, 12..13),
            (ForallTypeBinder, 13..15),
        ];
        if suffix == " @:@ T" {
            expected.extend([
                (Whitespace, 15..16),
                (Error, 16..17),
                (Colon, 17..18),
                (Error, 18..19),
                (Whitespace, 19..20),
                (TypeExpression, 20..21),
            ]);
        }
        assert_eq!(direct_kind_ranges(&forall), expected, "{source:?}");
        let binders = forall
            .children()
            .filter(|node| node.kind() == ForallTypeBinder)
            .collect::<Vec<_>>();
        let expected_binders = [
            vec![(Whitespace, 3..4), (Error, 4..5)],
            vec![(Missing, 5..5), (SigilIdentifier, 5..7)],
            vec![(Error, 7..8)],
            vec![(Error, 8..9)],
            vec![(Missing, 9..9), (SigilIdentifier, 9..11)],
            vec![(Missing, 13..13), (SigilIdentifier, 13..15)],
        ];
        assert_eq!(binders.len(), expected_binders.len(), "{source:?}");
        for (binder, expected) in binders.iter().zip(expected_binders) {
            assert_eq!(binder.parent(), Some(forall.clone()));
            assert_eq!(direct_kind_ranges(binder), expected, "{source:?}");
        }
        // Wrapper boundaries separate the adjacent separator Error groups;
        // the recovered binder separates the two direct Colon Error groups.
        // Only actual-binder gaps are Missing, including on terminal exits.
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == Missing)
                .map(|node| {
                    assert_eq!(node.parent().unwrap().kind(), ForallTypeBinder);
                    usize::from(node.text_range().start())
                })
                .collect::<Vec<_>>(),
            [5, 9, 13],
            "{source:?}"
        );
        assert!(
            forall
                .descendants_with_tokens()
                .filter(|child| child.kind() == Error)
                .all(|child| child.as_token().is_some())
        );
        assert!(!forall.descendants().any(|node| node.kind() == Invalid));
        if matches!(suffix, " " | "\n") {
            let trailing = root.last_token().unwrap();
            assert_eq!(trailing.parent(), Some(root.clone()));
            assert_eq!(usize::from(trailing.text_range().start()), 15);
            assert_eq!(usize::from(trailing.text_range().end()), source.len());
        }
    }
}

#[test]
fn forall_head_composition_first_actual_binder_owns_its_gap() {
    use SyntaxKind::*;

    let root = forall_cst("for'a:T");
    let forall = direct_forall(&root);
    assert_eq!(
        direct_kind_ranges(&forall),
        [
            (ForKw, 0..3),
            (ForallTypeBinder, 3..5),
            (Colon, 5..6),
            (TypeExpression, 6..7),
        ]
    );
    let binder = forall.children().next().unwrap();
    assert_eq!(
        direct_kind_ranges(&binder),
        [(Missing, 3..3), (SigilIdentifier, 3..5)]
    );
    assert_eq!(binder.parent(), Some(forall));
}

#[test]
fn forall_head_composition_terminal_exits_emit_only_the_current_slot() {
    use SyntaxKind::*;

    for (source, expected, expected_binders) in [
        (
            "for",
            vec![(ForKw, 0..3), (ForallTypeBinder, 3..3)],
            vec![vec![(Missing, 3..3)]],
        ),
        (
            "for @",
            vec![(ForKw, 0..3), (ForallTypeBinder, 3..5)],
            vec![vec![(Whitespace, 3..4), (Error, 4..5)]],
        ),
        (
            "for 'a",
            vec![(ForKw, 0..3), (ForallTypeBinder, 3..6), (Missing, 6..6)],
            vec![vec![(Whitespace, 3..4), (SigilIdentifier, 4..6)]],
        ),
        (
            "for 'a,",
            vec![
                (ForKw, 0..3),
                (ForallTypeBinder, 3..6),
                (ForallTypeBinder, 6..7),
                (Missing, 7..7),
            ],
            vec![
                vec![(Whitespace, 3..4), (SigilIdentifier, 4..6)],
                vec![(Error, 6..7)],
            ],
        ),
        (
            "for 'a:@",
            vec![
                (ForKw, 0..3),
                (ForallTypeBinder, 3..6),
                (Colon, 6..7),
                (Error, 7..8),
            ],
            vec![vec![(Whitespace, 3..4), (SigilIdentifier, 4..6)]],
        ),
    ] {
        let root = forall_cst(source);
        let forall = direct_forall(&root);
        assert_eq!(direct_kind_ranges(&forall), expected, "{source:?}");
        let binders = forall
            .children()
            .filter(|node| node.kind() == ForallTypeBinder)
            .collect::<Vec<_>>();
        assert_eq!(binders.len(), expected_binders.len(), "{source:?}");
        for (binder, expected) in binders.iter().zip(expected_binders) {
            assert_eq!(binder.parent(), Some(forall.clone()));
            assert_eq!(direct_kind_ranges(binder), expected, "{source:?}");
        }
        assert!(
            forall
                .descendants_with_tokens()
                .filter(|child| child.kind() == Error)
                .all(|child| child.as_token().is_some())
        );
        assert!(!forall.descendants().any(|node| node.kind() == Invalid));
    }
}

#[test]
fn forall_semantic_binder_slots_use_only_direct_wrapper_order() {
    use SyntaxKind::*;

    let root = forall_cst("for : T");
    let forall = direct_forall(&root);
    assert_eq!(
        direct_kind_ranges(&forall),
        [
            (ForKw, 0..3),
            (Whitespace, 3..4),
            (ForallTypeBinder, 4..4),
            (Colon, 4..5),
            (Whitespace, 5..6),
            (TypeExpression, 6..7),
        ]
    );
    let binder = forall
        .children()
        .find(|node| node.kind() == ForallTypeBinder)
        .unwrap();
    assert_eq!(direct_kind_ranges(&binder), [(Missing, 4..4)]);

    // Native UTF-8 leading is outside the first incomplete wrapper's maximal
    // raw Error group; the later real binder is a separate direct sibling.
    let root = forall_cst("for /*é*/,@ 'a:T");
    let forall = direct_forall(&root);
    let binders = forall
        .children()
        .filter(|node| node.kind() == ForallTypeBinder)
        .collect::<Vec<_>>();
    assert_eq!(binders.len(), 2);
    assert_eq!(
        direct_kind_ranges(&binders[0]),
        [
            (Whitespace, 3..4),
            (BlockComment, 4..10),
            (Error, 10..11),
            (Error, 11..12)
        ]
    );
    assert_eq!(
        direct_kind_ranges(&binders[1]),
        [(Whitespace, 12..13), (SigilIdentifier, 13..15)]
    );
    assert_eq!(binders[0].parent(), Some(forall.clone()));
    assert!(
        binders[0]
            .children_with_tokens()
            .filter(|child| child.kind() == Error)
            .all(|child| child.as_token().is_some())
    );
}

#[test]
fn forall_semantic_binder_boundary_occurrences_keep_sibling_order() {
    use SyntaxKind::*;

    let root = forall_cst("for 'a,'b:T");
    let forall = direct_forall(&root);
    let binders = forall
        .children()
        .filter(|node| node.kind() == ForallTypeBinder)
        .collect::<Vec<_>>();
    assert_eq!(binders.len(), 3);
    assert_eq!(direct_kind_ranges(&binders[1]), [(Error, 6..7)]);
    assert_eq!(
        direct_kind_ranges(&binders[2]),
        [(Missing, 7..7), (SigilIdentifier, 7..9)]
    );
    assert_eq!(binders[1].parent(), Some(forall.clone()));
    assert_eq!(binders[2].parent(), Some(forall.clone()));

    // Trivia after a placeholder makes the retried binder distinct from the
    // adjacent Missing/SigilIdentifier boundary occurrence above.
    let root = forall_cst("for 'a, 'b:T");
    let forall = direct_forall(&root);
    let binders = forall
        .children()
        .filter(|node| node.kind() == ForallTypeBinder)
        .collect::<Vec<_>>();
    assert_eq!(direct_kind_ranges(&binders[1]), [(Error, 6..7)]);
    assert_eq!(
        direct_kind_ranges(&binders[2]),
        [(Whitespace, 7..8), (SigilIdentifier, 8..10)]
    );
    assert!(!binders[2].descendants().any(|node| node.kind() == Missing));
}

#[test]
fn forall_semantic_terminal_slots_use_direct_colon_order_and_ranges() {
    use SyntaxKind::*;

    let root = forall_cst("for 'a T");
    let forall = direct_forall(&root);
    assert_eq!(
        direct_kind_ranges(&forall),
        [
            (ForKw, 0..3),
            (ForallTypeBinder, 3..6),
            (Whitespace, 6..7),
            (Missing, 7..7),
            (TypeExpression, 7..8),
        ]
    );

    let root = forall_cst("for 'a @:@ T");
    let forall = direct_forall(&root);
    assert_eq!(
        direct_kind_ranges(&forall),
        [
            (ForKw, 0..3),
            (ForallTypeBinder, 3..6),
            (Whitespace, 6..7),
            (Error, 7..8),
            (Colon, 8..9),
            (Error, 9..10),
            (Whitespace, 10..11),
            (TypeExpression, 11..12),
        ]
    );

    let ordinary = direct_forall(&forall_cst("for 'a:T"));
    let pv = direct_forall(&forall_cst("for 'a:{b:B}"));
    let ordinary_colon = ordinary
        .children_with_tokens()
        .find(|child| child.kind() == Colon)
        .unwrap();
    let pv_colon = pv
        .children_with_tokens()
        .find(|child| child.kind() == Colon)
        .unwrap();
    assert_eq!(ordinary_colon.kind(), pv_colon.kind());
    assert_eq!(
        usize::from(ordinary_colon.text_range().start())
            ..usize::from(ordinary_colon.text_range().end()),
        6..7
    );
    assert_eq!(
        usize::from(pv_colon.text_range().start())..usize::from(pv_colon.text_range().end()),
        6..7
    );

    let root = forall_cst("for 'a:");
    let forall = direct_forall(&root);
    assert_eq!(
        direct_kind_ranges(&forall),
        [
            (ForKw, 0..3),
            (ForallTypeBinder, 3..6),
            (Colon, 6..7),
            (Missing, 7..7)
        ]
    );
}

#[test]
fn forall_first_binder_slot_is_ordered_directly_in_rowan() {
    use SyntaxKind::*;

    let forall = |source| {
        let (green, _) = run_type(source);
        let root = SyntaxNode::new_root(green);
        root.descendants()
            .find(|node| node.kind() == ForallType)
            .unwrap()
    };
    let children = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|child| (child.kind(), child.to_string()))
            .collect::<Vec<_>>()
    };

    let missing = forall("for: T");
    assert_eq!(
        children(&missing),
        vec![
            (ForKw, "for".into()),
            (ForallTypeBinder, "".into()),
            (Colon, ":".into()),
            (Whitespace, " ".into()),
            (TypeExpression, "T".into()),
        ]
    );
    let missing_binder = missing
        .children()
        .find(|node| node.kind() == ForallTypeBinder)
        .unwrap();
    assert_eq!(children(&missing_binder), vec![(Missing, "".into())]);

    let malformed = forall("for /*lead*/, T 'a:T");
    let malformed_children = children(&malformed);
    assert_eq!(malformed_children[0], (ForKw, "for".into()));
    assert_eq!(
        malformed_children[1],
        (ForallTypeBinder, " /*lead*/, T".into())
    );
    assert_eq!(malformed_children[2], (ForallTypeBinder, " 'a".into()));
    assert_eq!(malformed_children[3], (Colon, ":".into()));
    assert_eq!(malformed_children[4], (TypeExpression, "T".into()));
    let binder = malformed
        .children()
        .find(|node| node.kind() == ForallTypeBinder)
        .unwrap();
    let binder_children = binder.children_with_tokens().collect::<Vec<_>>();
    let error_at = binder_children
        .iter()
        .position(|child| child.kind() == Error)
        .expect("first binder raw Error");
    assert!(error_at > 0, "leading trivia remains outside the raw Error");
    assert!(
        binder_children[..error_at]
            .iter()
            .all(|child| child.kind() != Error)
    );
    assert!(binder_children[error_at].as_token().is_some());
    assert!(!malformed.descendants().any(|node| node.kind() == Invalid));

    let first = forall("for,@:T");
    let after_accepted = forall("for 'a,@:T");
    let first_children = children(&first);
    let after_accepted_children = children(&after_accepted);
    assert_eq!(
        first_children,
        vec![
            (ForKw, "for".into()),
            (ForallTypeBinder, ",@".into()),
            (Colon, ":".into()),
            (TypeExpression, "T".into()),
        ]
    );
    let first_binder = first
        .children()
        .find(|node| node.kind() == ForallTypeBinder)
        .unwrap();
    assert_eq!(
        children(&first_binder),
        vec![(Error, ",".into()), (Error, "@".into())]
    );
    assert_eq!(after_accepted_children[1], (ForallTypeBinder, " 'a".into()));
    let first_error = first
        .descendants_with_tokens()
        .find(|child| child.kind() == Error)
        .unwrap();
    let after_accepted_error = after_accepted
        .descendants_with_tokens()
        .find(|child| child.kind() == Error)
        .unwrap();
    assert_eq!(first_error.to_string(), ",");
    assert_eq!(after_accepted_error.to_string(), ",");
    assert!(
        after_accepted_error.text_range().start() > first_error.text_range().start(),
        "the same comma leaf follows an accepted binder"
    );
    for node in [&first, &after_accepted] {
        assert!(!node.descendants().any(|child| child.kind() == Invalid));
        assert!(
            node.descendants_with_tokens()
                .filter(|child| child.kind() == Error)
                .all(|child| child.as_token().is_some())
        );
    }

    assert_pending_forall(
        "for,@:T",
        " /*é*/with tail",
        crate::lexical::stops::STOP_WITH,
        &[forall_record(0, TypeRole::ForallBinder, 3..5, true)],
    );
}

#[test]
fn forall_terminal_colon_body_phase_is_ordered_directly_in_rowan() {
    use SyntaxKind::*;

    let parse_forall = |source| {
        let (green, _) = run_type(source);
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), source, "{source:?}");
        let forall = root
            .descendants()
            .find(|node| node.kind() == ForallType)
            .expect("forall type");
        (root, forall)
    };
    let children = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|child| (child.kind(), child.to_string()))
            .collect::<Vec<_>>()
    };

    let (root, forall) = parse_forall("for 'a:{b:B}");
    assert_eq!(
        children(&forall),
        vec![
            (ForKw, "for".into()),
            (ForallTypeBinder, " 'a".into()),
            (Colon, ":".into()),
            (TypeExpression, "{b:B}".into()),
        ]
    );
    assert!(!root.descendants().any(|node| node.kind() == Invalid));
    drop(root);

    let (root, forall) = parse_forall("for 'a T");
    assert_eq!(
        children(&forall),
        vec![
            (ForKw, "for".into()),
            (ForallTypeBinder, " 'a".into()),
            (Whitespace, " ".into()),
            (Missing, "".into()),
            (TypeExpression, "T".into()),
        ]
    );
    assert!(!root.descendants().any(|node| node.kind() == Invalid));
    drop(root);

    let (root, forall) = parse_forall("for 'a:");
    assert_eq!(
        children(&forall),
        vec![
            (ForKw, "for".into()),
            (ForallTypeBinder, " 'a".into()),
            (Colon, ":".into()),
            (Missing, "".into()),
        ]
    );
    assert!(!root.descendants().any(|node| node.kind() == Invalid));
    drop(root);

    let (root, forall) = parse_forall("for 'a:@ T");
    assert_eq!(
        children(&forall),
        vec![
            (ForKw, "for".into()),
            (ForallTypeBinder, " 'a".into()),
            (Colon, ":".into()),
            (Error, "@".into()),
            (Whitespace, " ".into()),
            (TypeExpression, "T".into()),
        ]
    );
    let error = forall
        .children_with_tokens()
        .find(|child| child.kind() == Error)
        .expect("raw body error");
    assert!(error.as_token().is_some());
    assert_eq!(error.parent().map(|parent| parent.kind()), Some(ForallType));
    assert!(!root.descendants().any(|node| node.kind() == Invalid));
    drop(root);

    let (root, forall) = parse_forall("for 'a @:T");
    assert_eq!(
        children(&forall),
        vec![
            (ForKw, "for".into()),
            (ForallTypeBinder, " 'a".into()),
            (Whitespace, " ".into()),
            (Error, "@".into()),
            (Colon, ":".into()),
            (TypeExpression, "T".into()),
        ]
    );
    let error = forall
        .children_with_tokens()
        .find(|child| child.kind() == Error)
        .expect("raw colon error");
    assert!(error.as_token().is_some());
    assert_eq!(error.parent().map(|parent| parent.kind()), Some(ForallType));
    assert!(!root.descendants().any(|node| node.kind() == Invalid));
}

#[test]
fn forall_later_binder_boundary_is_ordered_directly_in_rowan() {
    use SyntaxKind::*;

    let parse_forall = |source| {
        let (green, _) = run_type(source);
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), source, "{source:?}");
        assert!(
            !root
                .descendants()
                .any(|node| matches!(node.kind(), Error | Invalid)),
            "{source:?}"
        );
        let forall = root
            .descendants()
            .find(|node| node.kind() == ForallType)
            .expect("forall type");
        (root, forall)
    };
    let children = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|child| (child.kind(), child.to_string()))
            .collect::<Vec<_>>()
    };

    let (root, forall) = parse_forall("for 'a'b:T");
    assert_eq!(
        children(&forall),
        vec![
            (ForKw, "for".into()),
            (ForallTypeBinder, " 'a".into()),
            (ForallTypeBinder, "'b".into()),
            (Colon, ":".into()),
            (TypeExpression, "T".into()),
        ]
    );
    let binders = forall
        .children()
        .filter(|node| node.kind() == ForallTypeBinder)
        .collect::<Vec<_>>();
    assert_eq!(
        children(&binders[1]),
        vec![(Missing, "".into()), (SigilIdentifier, "'b".into())]
    );
    drop(root);

    let (root, forall) = parse_forall("for 'a,'b:T");
    assert_eq!(
        children(&forall),
        vec![
            (ForKw, "for".into()),
            (ForallTypeBinder, " 'a".into()),
            (ForallTypeBinder, ",".into()),
            (ForallTypeBinder, "'b".into()),
            (Colon, ":".into()),
            (TypeExpression, "T".into()),
        ]
    );
    let binders = forall
        .children()
        .filter(|node| node.kind() == ForallTypeBinder)
        .collect::<Vec<_>>();
    assert_eq!(children(&binders[1]), vec![(Error, ",".into())]);
    assert_eq!(
        children(&binders[2]),
        vec![(Missing, "".into()), (SigilIdentifier, "'b".into())]
    );
    drop(root);

    let (root, forall) = parse_forall("for 'a, 'b:T");
    assert_eq!(
        children(&forall),
        vec![
            (ForKw, "for".into()),
            (ForallTypeBinder, " 'a".into()),
            (ForallTypeBinder, ",".into()),
            (ForallTypeBinder, " 'b".into()),
            (Colon, ":".into()),
            (TypeExpression, "T".into()),
        ]
    );
    let binders = forall
        .children()
        .filter(|node| node.kind() == ForallTypeBinder)
        .collect::<Vec<_>>();
    assert_eq!(children(&binders[1]), vec![(Error, ",".into())]);
    assert!(
        !binders[2].descendants().any(|node| node.kind() == Missing),
        "the retried binder has no boundary Missing"
    );
    drop(root);

    let (_root, forall) = parse_forall("for 'a,:T");
    assert_eq!(
        children(&forall),
        vec![
            (ForKw, "for".into()),
            (ForallTypeBinder, " 'a".into()),
            (ForallTypeBinder, ",".into()),
            (Colon, ":".into()),
            (TypeExpression, "T".into()),
        ]
    );

    let (_root, forall) = parse_forall("for 'a, T");
    assert_eq!(
        children(&forall),
        vec![
            (ForKw, "for".into()),
            (ForallTypeBinder, " 'a".into()),
            (ForallTypeBinder, ",".into()),
            (Whitespace, " ".into()),
            (Missing, "".into()),
            (TypeExpression, "T".into()),
        ]
    );
    let binders = forall
        .children()
        .filter(|node| node.kind() == ForallTypeBinder)
        .collect::<Vec<_>>();
    assert_eq!(children(&binders[1]), vec![(Error, ",".into())]);
}

#[test]
fn forall_missing_records_cover_only_the_current_mandatory_slot() {
    use TypeRole::{
        ForallBinder as B, ForallBinderBoundary as G, ForallBody as T, ForallColon as C,
    };
    for origin in [0, 41] {
        for (source, role, at) in [
            ("for", B, 3),
            ("for ", B, 3),
            ("for\n", B, 3),
            ("for 'a", C, 6),
            ("for 'a ", C, 6),
            ("for 'a:", T, 7),
            ("for 'a: ", T, 7),
            ("for'a:T", G, 3),
            ("for 'a'b:T", G, 6),
            ("for: T", B, 3),
            ("for : T", B, 4),
            ("for 'a T", C, 7),
        ] {
            let expected = [forall_record(0, role, origin + at..origin + at, false)];
            let root = assert_complete_type_recovery(source, origin, &expected);
            assert_typed_nodes(&root, &expected);
            if source.ends_with(' ') || source.ends_with('\n') {
                let trailing = root.last_token().unwrap();
                assert_eq!(trailing.parent().unwrap().kind(), SyntaxKind::Root);
            }
            if source == "for : T" {
                let binder = root
                    .descendants()
                    .find(|node| node.kind() == SyntaxKind::ForallTypeBinder)
                    .unwrap();
                assert!(binder.text().is_empty());
            }
        }
    }
}

#[test]
fn forall_forward_errors_have_phase_owned_roles_and_native_extents() {
    use TypeRole::{
        ForallBinder as B, ForallBinderBoundary as G, ForallBody as T, ForallColon as C,
    };
    for origin in [0, 41] {
        for (source, role, range, text) in [
            ("for @", B, 4..5, "@"),
            ("for @ 'a:T", B, 4..5, "@"),
            ("for @:T", B, 4..5, "@"),
            ("for T", B, 4..5, "T"),
            ("for $a", B, 4..6, "$a"),
            ("for &a", B, 4..6, "&a"),
            ("for _a", B, 4..6, "_a"),
            ("for, T", B, 3..6, ", T"),
            ("for; T", B, 3..6, "; T"),
            ("for,,;", B, 3..6, ",,;"),
            ("for 'a, 'b:T", G, 6..7, ","),
            ("for 'a @", C, 7..8, "@"),
            ("for 'a @:T", C, 7..8, "@"),
            ("for 'a @ T", C, 7..8, "@"),
            ("for 'a @ 'b:T", C, 7..8, "@"),
            ("for 'a @ 'b", C, 7..8, "@"),
            ("for 'a @, 'b:T", C, 7..9, "@,"),
            ("for 'a: @", T, 8..9, "@"),
            ("for 'a: @ T", T, 8..9, "@"),
            ("for 'a: @/*é*/T", T, 8..9, "@"),
            ("for (@: T) 'a:T", B, 4..10, "(@: T)"),
            ("for (@\n) 'a:T", B, 4..8, "(@\n)"),
        ] {
            let expected = [forall_record(
                0,
                role,
                origin + range.start..origin + range.end,
                true,
            )];
            let root = assert_complete_type_recovery(source, origin, &expected);
            assert_typed_nodes(&root, &expected);
            let error = recovery_groups(&root).into_iter().next().unwrap();
            assert_eq!(error.text(), text, "{source:?}");
            assert_eq!(
                error.parent().unwrap().kind(),
                if matches!(role, B | G) {
                    SyntaxKind::ForallTypeBinder
                } else {
                    SyntaxKind::ForallType
                }
            );
            if text.contains('(') {
                assert!(
                    error
                        .children_with_tokens()
                        .any(|node| node.kind() == SyntaxKind::Error && node.to_string() == "(")
                );
                assert!(
                    error
                        .children_with_tokens()
                        .any(|node| node.kind() == SyntaxKind::Error && node.to_string() == ")")
                );
            }
        }
    }
}

#[test]
fn forall_boundary_recovery_does_not_replace_the_distinct_colon_or_binder_gap() {
    use TypeRole::{ForallBinderBoundary as G, ForallColon as C};
    for (source, expected) in [
        (
            "for 'a, T",
            vec![
                forall_record(0, G, 6..7, true),
                forall_record(1, C, 8..8, false),
            ],
        ),
        (
            "for 'a,",
            vec![
                forall_record(0, G, 6..7, true),
                forall_record(1, C, 7..7, false),
            ],
        ),
        (
            "for 'a,'b:T",
            vec![
                forall_record(0, G, 6..7, true),
                forall_record(1, G, 7..7, false),
            ],
        ),
    ] {
        let root = assert_complete_type_recovery(source, 0, &expected);
        assert_typed_nodes(&root, &expected);
    }
}

#[test]
fn forall_literal_colon_and_full_canonical_bodies_remain_accepted() {
    for source in [
        "for 'a:{b:B}",
        "for 'a: {b:B}",
        "for 'a: :{A}",
        "for 'a: '[A]",
        "for 'a: [e] T",
        "for 'a: for 'b: 'a",
        "for/*é*/'a: Pair('a, B)::C -> D",
        "for\n  'a\n  'b:\n    Pair('a, 'b)",
        "(for 'a: T)::Next",
        "F(for 'a: T)",
    ] {
        let root = assert_complete_type_recovery(source, 0, &[]);
        assert_typed_nodes(&root, &[]);
    }
    for (source, expected) in [
        (
            "for 'a :{A}",
            vec![field_record(0, TypeRole::RecordFieldColon, 10..10, false)],
        ),
        (
            "for 'a @ :{A}",
            vec![
                forall_record(0, TypeRole::ForallColon, 7..8, true),
                field_record(1, TypeRole::RecordFieldColon, 12..12, false),
            ],
        ),
        (
            "for 'a @ : :{A}",
            vec![forall_record(0, TypeRole::ForallColon, 7..8, true)],
        ),
    ] {
        let root = assert_complete_type_recovery(source, 0, &expected);
        assert_typed_nodes(&root, &expected);
        let pv = source.contains(": :{");
        assert_eq!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::PolymorphicVariantType),
            pv
        );
        assert_eq!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::NamedRecordType),
            !pv
        );
    }
}

fn assert_pending_forall(
    prefix: &str,
    suffix: &str,
    stops: Stops,
    expected: &[CommittedRecoveryRecord],
) {
    let source = format!("{prefix}{suffix}");
    let frozen = frozen_recovery_ids(expected);
    let mut fresh_green = None;
    for (input, records) in [
        (None, expected),
        (Some(frozen.as_slice()), frozen.as_slice()),
    ] {
        let run = run_contextual_type_snapshot(
            &source,
            crate::type_expr::TypeMlContext::INACTIVE,
            stops,
            0,
            0,
            LineEntry::InLine,
            None,
            input,
        );
        assert_eq!(
            run.green.to_string(),
            format!("sentinel{prefix}"),
            "{source:?}"
        );
        assert_eq!(run.records, records, "{source:?}");
        assert_eq!(run.slots, records.len());
        assert_eq!(
            run.diagnostics,
            (
                Some(records.last().map_or(0, |record| record.id.0 + 1)),
                if input.is_some() { records.len() } else { 0 }
            )
        );
        if let Some(green) = &fresh_green {
            assert_eq!(&run.green, green);
        } else {
            fresh_green = Some(run.green.clone());
        }
        assert_typed_nodes(&SyntaxNode::new_root(run.green), records);
        let NormalizedExit::Complete(Err(Either::Left(pending)), line) = run.exit else {
            panic!("forall must return the complete pending Item: {source:?}")
        };
        let (control, origin, control_line, remainder, _, _) =
            scan_type_item_control(suffix, prefix.len(), &OperatorTable::empty());
        assert_eq!(pending, control, "{source:?}");
        assert_eq!(run.successor_origin, origin);
        assert_eq!(run.remainder, remainder);
        assert_eq!(line, control_line);
        assert_eq!(run.mark, ());
        assert!(run.same_operators);
    }
}

#[test]
fn forall_pending_callers_and_unclaimed_closes_keep_leading_and_no_cascade() {
    use TypeRole::{ForallBinder as B, ForallBody as T, ForallColon as C};
    for (prefix, role, range, error) in [
        ("for", B, 3..3, false),
        ("for 'a", C, 6..6, false),
        ("for 'a:", T, 7..7, false),
        ("for @", B, 4..5, true),
        ("for 'a @", C, 7..8, true),
        ("for 'a: @", T, 8..9, true),
    ] {
        let expected = [forall_record(0, role, range, error)];
        assert_pending_forall(
            prefix,
            " /*é*/with tail",
            crate::lexical::stops::STOP_WITH,
            &expected,
        );
        assert_pending_forall(prefix, " /*é*/) tail", 0, &expected);
        assert_pending_forall(prefix, "\n'b:T", 0, &expected);
        assert_pending_forall(prefix, ", T", crate::lexical::stops::STOP_COMMA, &expected);
    }
}

#[test]
fn forall_nested_error_handoffs_are_not_reopened_after_the_matching_stack() {
    use TypeRole::ForallBinder as B;
    for (suffix, stops) in [
        (":):T", STOP_COLON),
        ("with):T", crate::lexical::stops::STOP_WITH),
        ("with:A)", crate::lexical::stops::STOP_WITH),
        (", A)", crate::lexical::stops::STOP_COMMA),
    ] {
        assert_pending_forall("for (", suffix, stops, &[forall_record(0, B, 4..5, true)]);
    }
    assert_pending_forall("for (@", "\n'b:T", 0, &[forall_record(0, B, 4..6, true)]);
    assert_pending_forall("for ([", ")] 'a:T", 0, &[forall_record(0, B, 4..6, true)]);
    // Only a local head colon overrides this caller; the body must return it.
    assert_pending_forall(
        "for 'a:",
        " : T",
        STOP_COLON,
        &[forall_record(0, TypeRole::ForallBody, 7..7, false)],
    );
}

#[test]
fn forall_contextual_head_boundary_is_suspended_only_for_the_body() {
    use crate::type_expr::TypeOuterBoundary;
    for (prefix, suffix, role, range, error) in [
        (
            "for",
            " /*é*/with tail",
            TypeRole::ForallBinder,
            3..3,
            false,
        ),
        ("for 'a", " with tail", TypeRole::ForallColon, 6..6, false),
        ("for (", "with):T", TypeRole::ForallBinder, 4..5, true),
    ] {
        let source = format!("{prefix}{suffix}");
        let expected = [forall_record(0, role, range, error)];
        let frozen = frozen_recovery_ids(&expected);
        for (input, records) in [
            (None, expected.as_slice()),
            (Some(frozen.as_slice()), frozen.as_slice()),
        ] {
            let (green, exit, found, origin, remainder, actual, slots, diagnostics) =
                run_required_type_with_outer_boundary_and_recoveries(
                    &source,
                    TypeOuterBoundary::WITH,
                    false,
                    input,
                );
            assert_eq!(green.to_string(), prefix);
            assert!(found);
            assert_eq!(actual, records);
            assert_eq!(slots, records.len());
            assert_eq!(
                diagnostics,
                (
                    Some(records[0].id.0 + 1),
                    if input.is_some() { 1 } else { 0 }
                )
            );
            let NormalizedExit::Complete(Err(Either::Left(pending)), line) = exit else {
                panic!("contextual caller must stay pending")
            };
            let (control, control_origin, control_line, control_remainder, _, _) =
                scan_type_item_control(suffix, prefix.len(), &OperatorTable::empty());
            assert_eq!(pending, control);
            assert_eq!(origin, control_origin);
            assert_eq!(line, control_line);
            assert_eq!(remainder, control_remainder);
        }
    }
    for source in ["for 'a: with", "for 'a: for 'b: with"] {
        let (green, exit, found, origin, remainder, records, slots, diagnostics) =
            run_required_type_with_outer_boundary_and_recoveries(
                source,
                TypeOuterBoundary::WITH,
                false,
                None,
            );
        assert_eq!(green.to_string(), source);
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
        assert!(found);
        assert_eq!(origin, source.len());
        assert_eq!(remainder, "");
        assert!(records.is_empty());
        assert_eq!(slots, 0);
        assert_eq!(diagnostics, (Some(0), 0));
    }
}

#[test]
fn forall_fence_handoffs_preserve_the_abstract_coordinate_and_full_item() {
    use TypeRole::{ForallBinder as B, ForallBody as T, ForallColon as C};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (prefix, role, range, error) in [
        ("> > for", B, 9..9, false),
        ("> > for 'a", C, 12..12, false),
        ("> > for 'a:", T, 13..13, false),
        ("> > for @", B, 8..9, true),
        ("> > for 'a @", C, 11..12, true),
        ("> > for 'a: @", T, 12..13, true),
    ] {
        let source = format!("{prefix}\r\n> > ```\nouter");
        let expected = [forall_record(0, role, range, error)];
        let frozen = frozen_recovery_ids(&expected);
        let mut fresh = None;
        for (input, records) in [
            (None, expected.as_slice()),
            (Some(frozen.as_slice()), frozen.as_slice()),
        ] {
            let (green, exit, remainder, actual) = run_type_normalized_with_recoveries(
                &source,
                0,
                LineEntry::PhysicalStart,
                Some(&fence),
                input,
            );
            assert_eq!(green.to_string(), prefix);
            assert_eq!(actual, records, "{prefix:?}");
            assert_typed_nodes(&SyntaxNode::new_root(green.clone()), records);
            assert_eq!(remainder, "> > ```\nouter");
            let Some(NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart)) =
                exit
            else {
                panic!("forall must return the abstract fence Item")
            };
            assert_eq!(
                item.payload_view().pending_boundary().unwrap().coordinate(),
                prefix.len() + 2
            );
            assert!(item.leading_view().has_ordinary_newline());
            if let Some((fresh_green, fresh_item)) = &fresh {
                assert_eq!(&green, fresh_green);
                assert_eq!(&item, fresh_item);
            } else {
                fresh = Some((green, item));
            }
        }
    }
}

#[test]
fn forall_nested_in_structured_pv_errors_keeps_parent_before_child_records() {
    use TypeRole::{ForallBinder as B, ForallBody as T, ForallColon as C};
    for (source, end, role, range, error) in [
        (":{for}", 5, B, 5..5, false),
        (":{for 'a}", 8, C, 8..8, false),
        (":{for 'a:}", 9, T, 9..9, false),
        (":{for @}", 7, B, 6..7, true),
        (":{for 'a @}", 10, C, 9..10, true),
        (":{for 'a: @}", 11, T, 10..11, true),
    ] {
        let expected = [
            expected_type_error(0, TypeRole::PolymorphicVariantTagName, 2..end),
            forall_record(1, role, range, error),
        ];
        let root = assert_complete_type_recovery(source, 0, &expected);
        assert_typed_nodes(&root, &expected);
        let forall = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .unwrap();
        assert!(
            forall
                .ancestors()
                .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
        );
        let close = root.last_token().unwrap();
        assert_eq!(close.kind(), SyntaxKind::RBrace);
        assert!(
            !close
                .parent()
                .unwrap()
                .ancestors()
                .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
        );
    }
}

#[test]
fn forall_returns_actual_call_closes_and_iterates_long_local_punctuation() {
    for (source, role, at) in [
        ("F(for)", TypeRole::ForallBinder, 5),
        ("F(for 'a)", TypeRole::ForallColon, 8),
        ("F(for 'a:)", TypeRole::ForallBody, 9),
    ] {
        let expected = [forall_record(0, role, at..at, false)];
        let root = assert_complete_type_recovery(source, 0, &expected);
        assert_typed_nodes(&root, &expected);
        assert_eq!(
            root.last_token().unwrap().parent().unwrap().kind(),
            SyntaxKind::TypeCallClose
        );
        assert_eq!(
            root.last_token()
                .unwrap()
                .parent()
                .unwrap()
                .parent()
                .unwrap()
                .kind(),
            SyntaxKind::TypeCallTail
        );
    }
    let source = format!("for{}", ",".repeat(1024));
    let expected = [forall_record(0, TypeRole::ForallBinder, 3..1027, true)];
    let root = assert_complete_type_recovery(&source, 0, &expected);
    assert_typed_nodes(&root, &expected);
    let source = format!("for 'a{}:T", ",".repeat(512));
    let expected = (0..512)
        .map(|index| {
            forall_record(
                index,
                TypeRole::ForallBinderBoundary,
                6 + index as usize..7 + index as usize,
                true,
            )
        })
        .collect::<Vec<_>>();
    let root = assert_complete_type_recovery(&source, 0, &expected);
    assert_typed_nodes(&root, &expected);
}

//! Direct Rowan evidence for the `TypePathTail` PathSegment slot.
//!
//! These tests intentionally discard the legacy recovery ledger: ownership,
//! spelling, and insertion positions are asserted from the produced tree.

use super::*;

use crate::{
    SourceText, SyntaxEnvironment,
    lexical::yumark::{FenceOpener, FencePrefixPolicy},
    parse_file, scan_header,
    type_expr::TypeOuterBoundary,
};

fn node_range(node: &SyntaxNode) -> std::ops::Range<usize> {
    usize::from(node.text_range().start())..usize::from(node.text_range().end())
}

fn type_path_tails(root: &SyntaxNode) -> Vec<SyntaxNode> {
    root.descendants()
        .filter(|node| node.kind() == SyntaxKind::TypePathTail)
        .collect()
}

fn run_with_outer_boundary(
    source: &str,
    boundary: TypeOuterBoundary,
) -> (GreenNode, NormalizedExit, String) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let (primary, primary_successor, line_entry) = crate::type_expr::type_nud_item_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        0,
        LineEntry::InLine,
        None,
    );
    let (mut exit, accepted) =
        crate::type_expr::required_type_expr_with_caller_stops_and_outer_boundary_normalized(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            primary,
            0,
            0,
            boundary,
            primary_successor,
            line_entry,
            None,
        );
    assert!(
        accepted,
        "outer-boundary fixture admits its primary: {source:?}"
    );
    if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
        emit_end(&mut output, end);
    }
    output.finish_node();
    (
        finish_with_discarded_recoveries(output, recover),
        exit,
        input.to_owned(),
    )
}

fn run_with_close_stop(source: &str) -> (GreenNode, NormalizedExit) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let (exit, _) = crate::type_expr::type_expr_with_caller_stops_for_test(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        crate::lexical::stops::stops_for(TokenKind::RParen),
        0,
        0,
    )
    .expect("admitted TypePathTail fixture");
    output.finish_node();
    (finish_with_discarded_recoveries(output, recover), exit)
}

#[test]
fn type_path_tail_cst_admits_identifier_and_sigil_but_marks_integer_as_raw_error() {
    let source = "A::Name::'sigil";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let tails = type_path_tails(&root);
    assert_eq!(tails.len(), 2);
    assert_eq!(tails[0].parent(), tails[1].parent());
    assert_eq!(
        tails[0]
            .parent()
            .expect("TypeExpression owner")
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypePathTail)
            .collect::<Vec<_>>(),
        tails
    );
    assert_eq!(node_range(&tails[0]), 1..7);
    assert_eq!(node_range(&tails[1]), 7..15);
    assert_eq!(
        tails[0]
            .children_with_tokens()
            .map(|element| (element.kind(), element.to_string()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Identifier, "Name".to_owned()),
        ]
    );
    assert_eq!(
        tails[1]
            .children_with_tokens()
            .map(|element| (element.kind(), element.to_string()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::SigilIdentifier, "'sigil".to_owned()),
        ]
    );

    let source = "A::123";
    let (green, _) = run_type(source);
    assert_eq!(green.to_string(), source);
    let root = SyntaxNode::new_root(green);
    let tail = type_path_tails(&root).pop().expect("TypePathTail");
    assert_eq!(node_range(&tail), 1..6);
    assert_eq!(
        tail.children_with_tokens()
            .map(|element| (element.kind(), element.to_string()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Error, "123".to_owned()),
        ]
    );
}

#[test]
fn type_path_tail_cst_keeps_initial_and_raw_error_leading_in_distinct_phases() {
    for (source, expected) in [
        (
            "A:: ",
            vec![
                (SyntaxKind::ColonColon, "::"),
                (SyntaxKind::Whitespace, " "),
                (SyntaxKind::Missing, ""),
            ],
        ),
        (
            "A:: @",
            vec![
                (SyntaxKind::ColonColon, "::"),
                (SyntaxKind::Whitespace, " "),
                (SyntaxKind::Error, "@"),
            ],
        ),
    ] {
        let (green, _) = run_type(source);
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green);
        let tail = type_path_tails(&root).pop().expect("TypePathTail");
        assert_eq!(
            tail.children_with_tokens()
                .map(|element| (element.kind(), element.to_string()))
                .collect::<Vec<_>>(),
            expected
                .into_iter()
                .map(|(kind, text)| (kind, text.to_owned()))
                .collect::<Vec<_>>(),
            "{source:?}"
        );
        let missing = tail
            .last_child()
            .filter(|node| node.kind() == SyntaxKind::Missing);
        if let Some(missing) = missing {
            assert_eq!(node_range(&missing), source.len()..source.len());
            assert_eq!(missing.parent(), Some(tail.clone()));
        }
    }

    let source = "A:: )";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), "A:: ");
    let root = SyntaxNode::new_root(green);
    let tail = type_path_tails(&root).pop().expect("TypePathTail");
    assert_eq!(tail.to_string(), ":: ");
    assert_eq!(node_range(&tail.last_child().expect("Missing")), 4..4);
    let Some(Err(Either::Left(mut close))) = exit else {
        panic!("active close remains outside TypePathTail");
    };
    assert_eq!(close.payload_view().token_kind(), Some(TokenKind::RParen));
    assert_eq!(emit_pending_leading_text(&mut close), "");
}

#[test]
fn type_path_tail_cst_distinguishes_same_tail_retry_from_outer_type_apply() {
    for (source, retry_in_tail, retry_in_apply) in [
        ("A::@B", true, false),
        ("A::@ B", false, true),
        ("A::@/*c*/B", true, false),
        ("A::@/*c*/ B", false, true),
    ] {
        let (green, _) = run_type(source);
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green);
        let tail = type_path_tails(&root).pop().expect("TypePathTail");
        let errors = tail
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert!(!errors.is_empty(), "{source:?}");
        assert_eq!(errors[0].text(), "@", "{source:?}");
        let b = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == SyntaxKind::Identifier && token.text() == "B")
            .expect("retry B");
        assert_eq!(
            b.parent_ancestors().any(|node| node == tail),
            retry_in_tail,
            "{source:?}"
        );
        assert_eq!(
            b.parent_ancestors()
                .any(|node| node.kind() == SyntaxKind::TypeApplyArgument),
            retry_in_apply,
            "{source:?}"
        );
        if retry_in_apply {
            let gap = root
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
                .expect("outer apply gap");
            assert!(
                gap.parent_ancestors()
                    .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
            );
            assert!(!gap.parent_ancestors().any(|node| node == tail));
        }
    }
}

#[test]
fn type_path_tail_cst_gives_same_line_contextual_names_to_the_tail_but_keeps_newlines_outer() {
    let (green, exit, remainder) = run_with_outer_boundary("A::with", TypeOuterBoundary::WITH);
    assert_eq!(green.to_string(), "A::with");
    assert_eq!(remainder, "");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), _)
    ));
    let root = SyntaxNode::new_root(green);
    let tail = type_path_tails(&root).pop().expect("TypePathTail");
    assert_eq!(tail.to_string(), "::with");

    for gap in ["\n", "\r\n", "/*\n*/"] {
        let source = format!("A::{gap}with");
        let (green, exit, remainder) = run_with_outer_boundary(&source, TypeOuterBoundary::WITH);
        assert_eq!(green.to_string(), "A::", "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let NormalizedExit::Complete(Err(Either::Left(mut pending)), _) = exit else {
            panic!("newline contextual word stays outer: {source:?}");
        };
        assert_eq!(pending.payload_view().spelling(), Some("with"));
        assert_eq!(emit_pending_leading_text(&mut pending), gap, "{source:?}");
        let root = SyntaxNode::new_root(green);
        let tail = type_path_tails(&root).pop().expect("TypePathTail");
        assert_eq!(tail.to_string(), "::");
        let missing = tail.last_child().expect("PathSegment Missing");
        assert_eq!(
            (missing.kind(), node_range(&missing)),
            (SyntaxKind::Missing, 3..3)
        );
    }
}

#[test]
fn type_path_tail_cst_preserves_utf8_crlf_and_fence_boundaries_without_root_loss() {
    let source = "型::@\r\n  B";
    let (green, _) = run_type(source);
    assert_eq!(green.to_string(), source);
    let root = SyntaxNode::new_root(green);
    let tail = type_path_tails(&root).pop().expect("TypePathTail");
    assert_eq!(tail.to_string(), "::@\r\n  B");
    assert_eq!(node_range(&tail), 3..source.len());
    assert!(
        tail.children_with_tokens()
            .any(|element| element.kind() == SyntaxKind::Error && element.to_string() == "@")
    );

    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let source = "> > A::\n> > ```\nouter\n";
    let (green, exit, remainder) =
        run_type_normalized(source, 0, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), "> > A::");
    assert_eq!(remainder, "> > ```\nouter\n");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), _)) = exit else {
        panic!("fence remains pending");
    };
    assert!(boundary.payload_view().is_boundary());
    let root = SyntaxNode::new_root(green);
    let tail = type_path_tails(&root).pop().expect("TypePathTail");
    let missing = tail.last_child().expect("PathSegment Missing");
    assert_eq!(
        (missing.kind(), node_range(&missing)),
        (SyntaxKind::Missing, 7..7)
    );
}

#[test]
fn type_path_tail_cst_keeps_post_error_boundaries_and_comment_runs_distinct() {
    let (green, exit, remainder) = run_with_outer_boundary("A::@ with", TypeOuterBoundary::WITH);
    assert_eq!(green.to_string(), "A::@");
    assert_eq!(remainder, "");
    let NormalizedExit::Complete(Err(Either::Left(mut pending)), _) = exit else {
        panic!("post-Error contextual word remains outer");
    };
    assert_eq!(pending.payload_view().spelling(), Some("with"));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");
    let root = SyntaxNode::new_root(green);
    let tail = type_path_tails(&root).pop().expect("TypePathTail");
    assert_eq!(
        tail.children_with_tokens()
            .map(|element| (element.kind(), element.to_string()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Error, "@".to_owned()),
        ]
    );

    let (green, exit) = run_with_close_stop("A::@/*x*/ )");
    assert_eq!(green.to_string(), "A::@");
    let NormalizedExit::Complete(Err(Either::Left(mut close)), _) = exit else {
        panic!("comment-prefix close remains pending");
    };
    assert_eq!(close.payload_view().token_kind(), Some(TokenKind::RParen));
    assert_eq!(emit_pending_leading_text(&mut close), "/*x*/ ");

    let source = "A::@/*x*/@B";
    let (green, _) = run_type(source);
    assert_eq!(green.to_string(), source);
    let root = SyntaxNode::new_root(green);
    let tail = type_path_tails(&root).pop().expect("TypePathTail");
    assert_eq!(node_range(&tail), 1..source.len());
    assert_eq!(
        tail.children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Error, "@".to_owned()),
            (SyntaxKind::Error, "/*x*/".to_owned()),
            (SyntaxKind::Error, "@".to_owned()),
            (SyntaxKind::Identifier, "B".to_owned()),
        ]
    );
    let b = tail.last_token().expect("same-tail retry B");
    assert_eq!((b.kind(), b.text()), (SyntaxKind::Identifier, "B"));
}

#[test]
fn type_path_tail_cst_retains_layout_and_fence_boundaries_after_recovery() {
    for (source, emitted, pending_leading) in [("A::\nB", "A::\n", ""), ("A::@\nB", "A::@", "\n")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), emitted, "{source:?}");
        let Some(Err(Either::Left(mut pending))) = exit else {
            panic!("shallow newline remains pending: {source:?}");
        };
        assert_eq!(pending.payload_view().spelling(), Some("B"));
        assert_eq!(emit_pending_leading_text(&mut pending), pending_leading);
    }

    let (green, exit, remainder) = run_with_outer_boundary("A::\n  with", TypeOuterBoundary::WITH);
    assert_eq!(green.to_string(), "A::");
    assert_eq!(remainder, "");
    let NormalizedExit::Complete(Err(Either::Left(mut pending)), _) = exit else {
        panic!("deeper newline contextual word remains outer");
    };
    assert_eq!(pending.payload_view().spelling(), Some("with"));
    assert_eq!(emit_pending_leading_text(&mut pending), "\n  ");

    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let source = "> > A::@\n> > ```\nouter\n";
    let (green, exit, remainder) =
        run_type_normalized(source, 0, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), "> > A::@");
    assert_eq!(remainder, "> > ```\nouter\n");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), line)) = exit else {
        panic!("post-Error fence remains pending");
    };
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(line, LineEntry::PhysicalStart);
    assert_eq!(
        boundary
            .payload_view()
            .pending_boundary()
            .unwrap()
            .coordinate(),
        9
    );
    assert!(boundary.leading_view().has_ordinary_newline());
    assert_eq!(boundary.extent(9).recovery_range(), 8..9);
    let root = SyntaxNode::new_root(green);
    let tail = type_path_tails(&root).pop().expect("TypePathTail");
    assert_eq!(node_range(&tail), 5..8);
    assert_eq!(
        tail.children_with_tokens()
            .map(|element| (element.kind(), element.to_string()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Error, "@".to_owned()),
        ]
    );
}

#[test]
fn type_path_tail_cst_resumes_a_sibling_separator_after_a_malformed_segment() {
    let source = "A::@::B";
    let (green, _) = run_type(source);
    assert_eq!(green.to_string(), source);
    let root = SyntaxNode::new_root(green);
    let tails = type_path_tails(&root);
    assert_eq!(tails.len(), 2);
    assert_eq!(tails[0].to_string(), "::@");
    assert_eq!(tails[1].to_string(), "::B");
    assert_eq!(tails[0].parent(), tails[1].parent());
    assert_eq!(
        tails[0]
            .children_with_tokens()
            .map(|element| (element.kind(), element.to_string()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Error, "@".to_owned()),
        ]
    );
}

#[test]
fn public_root_keeps_type_path_error_and_eof_leading_losslessly() {
    use std::sync::Arc;

    let source: Arc<SourceText> = Arc::from("type T = A::@  ");
    let header = Arc::new(scan_header(Arc::clone(&source)));
    let parsed = parse_file(
        Arc::clone(&source),
        header,
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert_eq!(parsed.green().to_string(), source.as_ref());
    let root = SyntaxNode::new_root(parsed.green().clone());
    let tail = type_path_tails(&root).pop().expect("public TypePathTail");
    assert_eq!(tail.to_string(), "::@");
    assert_eq!(node_range(&tail), 10..13);
    assert_eq!(
        tail.last_token()
            .map(|token| (token.kind(), token.text().to_owned())),
        Some((SyntaxKind::Error, "@".to_owned()))
    );
    let eof_leading = root.last_token().expect("Root EOF leading").clone();
    assert_eq!(
        (eof_leading.kind(), eof_leading.text()),
        (SyntaxKind::Whitespace, "  ")
    );
    assert!(!eof_leading.parent_ancestors().any(|node| node == tail));
}

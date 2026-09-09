//! Direct Rowan evidence for the approved TypeCall terminal close boundary.
use super::*;

fn close_node(root: &SyntaxNode) -> SyntaxNode {
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .unwrap();
    let close = call.last_child().expect("terminal close node");
    assert_eq!(close.kind(), SyntaxKind::TypeCallClose);
    assert_eq!(
        call.children()
            .filter(|node| node.kind() == SyntaxKind::TypeCallClose)
            .count(),
        1
    );
    let terminals = close
        .children_with_tokens()
        .filter(|child| matches!(child.kind(), SyntaxKind::RParen | SyntaxKind::Missing))
        .collect::<Vec<_>>();
    assert_eq!(terminals.len(), 1);
    assert_eq!(close.last_child_or_token(), terminals.last().cloned());
    close
}

fn children(node: &SyntaxNode) -> Vec<(SyntaxKind, String)> {
    node.children_with_tokens()
        .map(|child| (child.kind(), child.to_string()))
        .collect()
}

#[test]
fn type_call_post_argument_residual_enters_irreversible_close() {
    for (source, errors) in [
        ("T(A@)", vec!["@"]),
        ("T(A@B)", vec!["@", "B"]),
        ("T(A@,B)", vec!["@", ",", "B"]),
        ("T(A@é)", vec!["@", "é"]),
        ("T(A@with)", vec!["@", "with"]),
    ] {
        let (green, _, remainder, records) =
            run_type_normalized_with_recoveries(source, 0, LineEntry::InLine, None, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(remainder, "");
        let root = SyntaxNode::new_root(green);
        let close = close_node(&root);
        let mut expected = errors
            .iter()
            .map(|text| (SyntaxKind::Error, (*text).to_owned()))
            .collect::<Vec<_>>();
        expected.push((SyntaxKind::RParen, ")".into()));
        assert_eq!(children(&close), expected, "{source}");
        assert!(records.iter().all(|record| record.site.role
            == GrammarRole::ClosingDelimiter {
                owner: ConstructRole::TypeCall,
                delimiter: Delimiter::Parenthesis
            }));
    }
}

#[test]
fn type_call_close_distinguishes_argument_and_close_errors_and_missing_slots() {
    for (source, direct, close_children) in [
        (
            "T(@)",
            vec![
                SyntaxKind::LParen,
                SyntaxKind::Error,
                SyntaxKind::TypeCallClose,
            ],
            vec![(SyntaxKind::RParen, ")")],
        ),
        (
            "T(])",
            vec![SyntaxKind::LParen, SyntaxKind::TypeCallClose],
            vec![(SyntaxKind::Error, "]"), (SyntaxKind::RParen, ")")],
        ),
        (
            "T(@])",
            vec![
                SyntaxKind::LParen,
                SyntaxKind::Error,
                SyntaxKind::TypeCallClose,
            ],
            vec![(SyntaxKind::Error, "]"), (SyntaxKind::RParen, ")")],
        ),
        (
            "T(",
            vec![
                SyntaxKind::LParen,
                SyntaxKind::Missing,
                SyntaxKind::TypeCallClose,
            ],
            vec![(SyntaxKind::Missing, "")],
        ),
    ] {
        let (green, _, _) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source);
        let close = close_node(&SyntaxNode::new_root(green));
        assert_eq!(
            close
                .parent()
                .unwrap()
                .children_with_tokens()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            direct
        );
        assert_eq!(
            children(&close),
            close_children
                .into_iter()
                .map(|(kind, text)| (kind, text.to_owned()))
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn type_call_close_accepted_nested_and_missing_path_controls() {
    for source in [
        "T()",
        "T(A)",
        "T(U(A),B,)",
        "T(A",
        "T(A,",
        "T(@",
        "T(@,",
        "T(A]@",
        "T(A@",
        "T(A@ ",
        "T(A@/*é*/",
        "T(A@\n",
        "T(A@\r\n",
    ] {
        let (green, _, _) = run_type_with_recoveries(source, None);
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green);
        close_node(&root);
        for call in root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeCallTail)
        {
            assert_eq!(
                call.last_child_or_token().unwrap().kind(),
                SyntaxKind::TypeCallClose,
                "{source}"
            );
        }
    }
}

#[test]
fn type_call_close_native_trivia_separates_close_errors() {
    for trivia in [" ", "/*é*/", "\n", "\r\n"] {
        let source = format!("T(A@{trivia}B)");
        let (green, _, _) = run_type_with_recoveries(&source, None);
        assert_eq!(green.to_string(), source);
        let close = close_node(&SyntaxNode::new_root(green));
        let parts = children(&close);
        assert_eq!(parts.first(), Some(&(SyntaxKind::Error, "@".into())));
        assert_eq!(parts[1].1, trivia);
        assert_ne!(parts[1].0, SyntaxKind::Error);
        assert_eq!(parts[2], (SyntaxKind::Error, "B".into()));
        assert_eq!(parts[3], (SyntaxKind::RParen, ")".into()));
    }
}

#[test]
fn type_call_close_residual_preserves_exact_caller_boundary() {
    for trivia in [" ", "/*é*/", "\n", "\r\n"] {
        let source = format!("T(A@{trivia}] tail");
        let operators = OperatorTable::empty();
        let mut input = source.as_str();
        let mut recover = Recover::new_for_test(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (exit, origin) = crate::type_expr::type_expr_with_caller_stops_for_test(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            crate::lexical::stops::stops_for(TokenKind::RBracket),
            0,
            0,
        )
        .unwrap();
        output.finish_node();
        let root = SyntaxNode::new_root(finish_with_discarded_recoveries(output, recover));
        let NormalizedExit::Complete(Err(Either::Left(pending)), line) = exit else {
            panic!("protected close")
        };
        let (control, control_origin, control_line, control_remainder, _, _) =
            scan_type_item_control(&source[4..], 4, &operators);
        assert_eq!(pending, control);
        assert_eq!(origin, control_origin);
        assert_eq!(line, control_line);
        assert_eq!(input, control_remainder);
        assert_eq!(root.to_string(), "T(A@");
        assert_eq!(
            children(&close_node(&root)),
            vec![
                (SyntaxKind::Error, "@".into()),
                (SyntaxKind::Missing, "".into())
            ]
        );
    }
}

#[test]
fn type_call_close_public_root_conserves_source_and_external_tail() {
    use crate::{SourceText, SyntaxEnvironment, parse_file, scan_header};
    let source: Arc<SourceText> = Arc::from("type X = T(A@/*é*/B)::C");
    let parsed = parse_file(
        Arc::clone(&source),
        Arc::new(scan_header(Arc::clone(&source))),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert_eq!(parsed.green().to_string(), source.as_ref());
    let root = SyntaxNode::new_root(parsed.green().clone());
    assert_eq!(close_node(&root).to_string(), "@/*é*/B)");
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::TypePathTail && node.to_string() == "::C")
    );
}

#[test]
fn type_call_close_residual_preserves_quoted_fence_and_outer_close() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for newline in ["\n", "\r\n"] {
        let source = format!("> > T(A@{newline}> > ```\nouter\n");
        let base = 41;
        let emitted = "> > T(A@";
        let (green, exit, remainder) =
            run_type_normalized(&source, base, LineEntry::PhysicalStart, Some(&fence));
        assert_eq!(green.to_string(), emitted);
        let Some(NormalizedExit::Complete(Err(Either::Left(pending)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("pending fence")
        };
        let coordinate = base + emitted.len() + newline.len();
        assert_eq!(
            pending
                .payload_view()
                .pending_boundary()
                .unwrap()
                .coordinate(),
            coordinate
        );
        assert_eq!(
            pending.extent(coordinate).recovery_range(),
            base + emitted.len()..coordinate
        );
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        pending.emit_terminal_boundary(&mut output);
        output.finish_node();
        assert_eq!(output.finish().to_string(), newline);
        assert_eq!(format!("{emitted}{newline}{remainder}"), source);
        assert_eq!(
            children(&close_node(&SyntaxNode::new_root(green))),
            vec![
                (SyntaxKind::Error, "@".into()),
                (SyntaxKind::Missing, "".into())
            ]
        );
    }
    let source = "{x:T(A@}";
    let (green, _, _) = run_type_with_recoveries(source, None);
    assert_eq!(green.to_string(), source);
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        children(&close_node(&root)),
        vec![
            (SyntaxKind::Error, "@".into()),
            (SyntaxKind::Missing, "".into())
        ]
    );
    assert_eq!(root.last_token().unwrap().kind(), SyntaxKind::RBrace);
}

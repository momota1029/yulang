//! Current-behavior evidence for the TypeCall close-slot architecture return.
//! This pins the reachable fallback, not a desired recovery topology.

use super::*;

#[test]
fn type_call_post_child_fallback_returns_unknown_without_close_publication() {
    let source = "T(A@)";
    let (green, exit, remainder, _records) =
        run_type_normalized_with_recoveries(source, 0, LineEntry::InLine, None, None);

    assert_eq!(green.to_string(), "T(A");
    assert_eq!(remainder, ")");
    let successor_origin = source.len() - remainder.len();
    assert_eq!(successor_origin, 4);
    let Some(NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine)) = exit
    else {
        panic!("post-child fallback must hand the unknown Item out unchanged")
    };
    assert_eq!(
        pending.payload_view().token_kind(),
        Some(TokenKind::Unknown)
    );
    assert_eq!(pending.payload_view().spelling(), Some("@"));
    assert_eq!(pending.extent(successor_origin).physical(), 3..4);
    assert_eq!(pending.extent(successor_origin).leading(), 3..3);
    assert_eq!(pending.extent(successor_origin).remaining(), 3..3);
    assert_eq!(pending.extent(successor_origin).payload(), 3..4);
    assert_eq!(emit_pending_leading_text(&mut pending), "");

    let root = SyntaxNode::new_root(green);
    let calls = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::TypeCallTail)
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 1);
    assert_eq!(
        calls[0]
            .children_with_tokens()
            .map(|element| (element.kind(), element.to_string()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::LParen, "(".to_owned()),
            (SyntaxKind::TypeExpression, "A".to_owned()),
        ]
    );
    assert_eq!(usize::from(calls[0].text_range().start()), 1);
    assert_eq!(usize::from(calls[0].text_range().end()), 3);
}

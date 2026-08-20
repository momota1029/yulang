//! Direct Rowan CST emission after a parser branch has committed.
//!
//! This sink deliberately has no parse-event buffer or rollback mechanism.
//! Rowan checkpoints only identify children that an accepted Pratt continuation
//! may wrap in a parent node.
//!
//! The token checks here are a debug-time sanity net: every token must borrow
//! from the original source, and consecutive token slices must be contiguous
//! and in source order. Whole-parse validation that tokens cover
//! `0..source.len()` exactly belongs to the later grammar-wiring slice, where a
//! complete parse makes that invariant meaningful.

use rowan::{Checkpoint, GreenNode, GreenNodeBuilder};

use crate::{session::DirectCstSink, syntax_kind::SyntaxKind};

/// Writes committed syntax nodes and source-backed tokens directly to Rowan.
pub(crate) struct RowanSink<'source> {
    builder: GreenNodeBuilder<'static>,
    source: &'source str,
    #[cfg(debug_assertions)]
    last_token_end: Option<usize>,
}

impl<'source> RowanSink<'source> {
    pub(crate) fn new(source: &'source str) -> Self {
        Self {
            builder: GreenNodeBuilder::new(),
            source,
            #[cfg(debug_assertions)]
            last_token_end: None,
        }
    }

    pub(crate) fn start_node(&mut self, kind: SyntaxKind) {
        self.builder.start_node(kind.into());
    }

    pub(crate) fn token(&mut self, kind: SyntaxKind, text: &'source str) {
        self.validate_token(text);
        self.builder.token(kind.into(), text);
    }

    pub(crate) fn finish_node(&mut self) {
        self.builder.finish_node();
    }

    pub(crate) fn checkpoint(&self) -> Checkpoint {
        self.builder.checkpoint()
    }

    pub(crate) fn start_node_at(&mut self, checkpoint: Checkpoint, kind: SyntaxKind) {
        self.builder.start_node_at(checkpoint, kind.into());
    }

    pub(crate) fn finish(self) -> GreenNode {
        self.builder.finish()
    }

    fn validate_token(&mut self, text: &'source str) {
        #[cfg(debug_assertions)]
        {
            let source_start = self.source.as_ptr() as usize;
            let source_end = source_start + self.source.len();
            let token_start = text.as_ptr() as usize;
            let token_end = token_start + text.len();

            debug_assert!(
                token_start >= source_start && token_end <= source_end,
                "token text must be a slice of the sink source"
            );
            if let Some(last_token_end) = self.last_token_end {
                debug_assert_eq!(
                    token_start, last_token_end,
                    "token emissions must be contiguous and in source order"
                );
            }
            self.last_token_end = Some(token_end);
        }
    }
}

impl DirectCstSink for RowanSink<'_> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SyntaxNode;

    #[test]
    fn builds_a_lossless_tree_directly() {
        let source = "use x";
        let mut sink = RowanSink::new(source);

        sink.start_node(SyntaxKind::Root);
        sink.token(SyntaxKind::UseKw, &source[0..3]);
        sink.token(SyntaxKind::Whitespace, &source[3..4]);
        sink.token(SyntaxKind::Identifier, &source[4..5]);
        sink.finish_node();

        assert_eq!(sink.finish().to_string(), source);
    }

    #[test]
    fn balanced_nested_nodes_finish_as_one_tree() {
        let source = "1";
        let mut sink = RowanSink::new(source);

        sink.start_node(SyntaxKind::Root);
        sink.start_node(SyntaxKind::IntegerLiteral);
        sink.token(SyntaxKind::Integer, source);
        sink.finish_node();
        sink.finish_node();

        let root = SyntaxNode::new_root(sink.finish());
        let literal = root.children().next().expect("integer literal node");
        assert_eq!(literal.kind(), SyntaxKind::IntegerLiteral);
        assert_eq!(literal.to_string(), source);
    }

    #[test]
    #[should_panic]
    fn rowan_rejects_an_unfinished_node() {
        let source = "x";
        let mut sink = RowanSink::new(source);

        sink.start_node(SyntaxKind::Root);
        sink.token(SyntaxKind::Identifier, source);
        let _ = sink.finish();
    }

    #[test]
    fn checkpoint_wraps_tokens_emitted_after_it() {
        let source = "ab";
        let mut sink = RowanSink::new(source);

        sink.start_node(SyntaxKind::Root);
        sink.token(SyntaxKind::Identifier, &source[0..1]);
        let checkpoint = sink.checkpoint();
        sink.token(SyntaxKind::Identifier, &source[1..2]);
        sink.start_node_at(checkpoint, SyntaxKind::IntegerLiteral);
        sink.finish_node();
        sink.finish_node();

        let root = SyntaxNode::new_root(sink.finish());
        let mut children = root.children_with_tokens();
        let first = children.next().expect("token before checkpoint");
        assert_eq!(first.kind(), SyntaxKind::Identifier);
        assert_eq!(
            first.as_token().expect("first child is a token").text(),
            "a"
        );

        let wrapped = children.next().expect("wrapped node");
        assert_eq!(wrapped.kind(), SyntaxKind::IntegerLiteral);
        let wrapped = wrapped.as_node().expect("second child is a node");
        assert_eq!(wrapped.to_string(), "b");
        assert_eq!(wrapped.first_token().expect("wrapped token").text(), "b");
        assert!(children.next().is_none());
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "token emissions must be contiguous and in source order")]
    fn rejects_overlapping_token_emissions_in_debug_builds() {
        let source = "abc";
        let mut sink = RowanSink::new(source);

        sink.start_node(SyntaxKind::Root);
        sink.token(SyntaxKind::Identifier, &source[0..2]);
        sink.token(SyntaxKind::Identifier, &source[1..2]);
    }
}

//! Direct Rowan CST emission after a parser branch has committed.
//!
//! This sink deliberately has no parse-event buffer or rollback mechanism.
//! Rowan checkpoints only identify children that an accepted Pratt continuation
//! may wrap in a parent node.
//!
//! Tokens always borrow from the original source. `finish_complete` verifies
//! that direct emission covered that source exactly once without keeping a
//! source-wide token or parse-event buffer.

use std::ops::Range;

use rowan::{Checkpoint, GreenNode, GreenNodeBuilder};

use crate::{
    scan::trivia::{TriviaPartKind, TriviaRun},
    session::DirectCstSink,
    syntax_kind::SyntaxKind,
};

/// Writes committed syntax nodes and source-backed tokens directly to Rowan.
pub(crate) struct RowanSink<'source> {
    builder: GreenNodeBuilder<'static>,
    source: &'source str,
    open_nodes: usize,
    first_token_start: Option<usize>,
    last_token_end: Option<usize>,
    contiguous_coverage: bool,
}

impl<'source> RowanSink<'source> {
    pub(crate) fn new(source: &'source str) -> Self {
        Self {
            builder: GreenNodeBuilder::new(),
            source,
            open_nodes: 0,
            first_token_start: None,
            last_token_end: None,
            contiguous_coverage: true,
        }
    }

    pub(crate) fn start_node(&mut self, kind: SyntaxKind) {
        self.builder.start_node(kind.into());
        self.open_nodes += 1;
    }

    pub(crate) fn token(&mut self, kind: SyntaxKind, text: &'source str) {
        let range = self.source_range(text);
        self.record_token_range(range);
        self.builder.token(kind.into(), text);
    }

    /// Emits a token directly from a byte range of this sink's source.
    pub(crate) fn token_range(&mut self, kind: SyntaxKind, range: Range<usize>) {
        self.validate_range(&range);
        self.record_token_range(range.clone());
        self.builder.token(kind.into(), &self.source[range]);
    }

    /// Emits every typed trivia part directly from the source ranges scanned
    /// by the shared trivia scanner.
    pub(crate) fn emit_trivia(&mut self, trivia: &TriviaRun) {
        for part in trivia.parts() {
            let kind = match part.kind() {
                TriviaPartKind::Whitespace => SyntaxKind::Whitespace,
                TriviaPartKind::Newline => SyntaxKind::Newline,
                TriviaPartKind::LineComment => SyntaxKind::LineComment,
                TriviaPartKind::BlockComment { .. } => SyntaxKind::BlockComment,
            };
            self.token_range(kind, part.range());
        }
    }

    pub(crate) fn finish_node(&mut self) {
        assert!(
            self.open_nodes > 0,
            "cannot finish a node that was not started"
        );
        self.builder.finish_node();
        self.open_nodes -= 1;
    }

    pub(crate) fn checkpoint(&self) -> Checkpoint {
        self.builder.checkpoint()
    }

    pub(crate) fn start_node_at(&mut self, checkpoint: Checkpoint, kind: SyntaxKind) {
        self.builder.start_node_at(checkpoint, kind.into());
        self.open_nodes += 1;
    }

    pub(crate) fn finish(self) -> GreenNode {
        self.builder.finish()
    }

    /// Finishes a complete, lossless source tree.
    ///
    /// Unlike [`Self::finish`], this checks that the caller closed every node
    /// and emitted the complete source exactly once.
    pub(crate) fn finish_complete(self) -> GreenNode {
        assert_eq!(
            self.open_nodes, 0,
            "all started syntax nodes must be finished before completion"
        );
        assert!(
            self.contiguous_coverage,
            "token emissions must be contiguous and in source order"
        );

        if self.source.is_empty() {
            assert!(
                self.first_token_start.is_none() && self.last_token_end.is_none(),
                "an empty source cannot emit tokens"
            );
        } else {
            assert_eq!(
                self.first_token_start,
                Some(0),
                "complete token coverage must start at byte zero"
            );
            assert_eq!(
                self.last_token_end,
                Some(self.source.len()),
                "complete token coverage must end at the source length"
            );
        }

        let source = self.source;
        let green = self.builder.finish();
        assert_eq!(
            green.to_string(),
            source,
            "the completed green tree must reproduce its source"
        );
        green
    }

    fn source_range(&self, text: &'source str) -> Range<usize> {
        let source_start = self.source.as_ptr() as usize;
        let source_end = source_start + self.source.len();
        let token_start = text.as_ptr() as usize;
        let token_end = token_start + text.len();

        assert!(
            token_start >= source_start && token_end <= source_end,
            "token text must be a slice of the sink source"
        );
        (token_start - source_start)..(token_end - source_start)
    }

    fn validate_range(&self, range: &Range<usize>) {
        assert!(
            range.start < range.end,
            "direct CST tokens must cover a non-empty source range"
        );
        assert!(
            range.end <= self.source.len(),
            "token range must stay within the sink source"
        );
        assert!(
            self.source.is_char_boundary(range.start) && self.source.is_char_boundary(range.end),
            "token range must align with UTF-8 character boundaries"
        );
    }

    fn record_token_range(&mut self, range: Range<usize>) {
        self.validate_range(&range);
        if let Some(last_token_end) = self.last_token_end {
            self.contiguous_coverage &= range.start == last_token_end;
        } else {
            self.first_token_start = Some(range.start);
        }
        self.last_token_end = Some(range.end);
    }
}

impl DirectCstSink for RowanSink<'_> {}

#[cfg(test)]
mod tests {
    use super::*;
    use chasa::{input::IsCut, prelude::from_fn};

    use crate::{
        SyntaxNode,
        input::SourceInput,
        scan::trivia::{TriviaRun, scan_trivia},
        session::ParseLocal,
    };

    fn scan_all_trivia(source: &str) -> TriviaRun {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut input = chasa::prelude::In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        input
            .run(from_fn(scan_trivia))
            .expect("trivia scanning is total")
    }

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
    fn token_range_and_completion_build_a_whole_source_tree() {
        let source = "use";
        let mut sink = RowanSink::new(source);

        sink.start_node(SyntaxKind::Root);
        sink.token_range(SyntaxKind::UseKw, 0..source.len());
        sink.finish_node();

        assert_eq!(sink.finish_complete().to_string(), source);
    }

    #[test]
    fn emit_trivia_preserves_each_typed_part_as_a_token() {
        let source = " \t// note\r\n/* nested /* block */ */";
        let trivia = scan_all_trivia(source);
        let mut sink = RowanSink::new(source);

        sink.start_node(SyntaxKind::Root);
        sink.emit_trivia(&trivia);
        sink.finish_node();

        let root = SyntaxNode::new_root(sink.finish_complete());
        let kinds = root
            .children_with_tokens()
            .map(|child| child.kind())
            .collect::<Vec<_>>();
        assert_eq!(
            kinds,
            vec![
                SyntaxKind::Whitespace,
                SyntaxKind::LineComment,
                SyntaxKind::Newline,
                SyntaxKind::BlockComment,
            ]
        );
        assert_eq!(root.to_string(), source);
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
    #[should_panic(expected = "all started syntax nodes must be finished before completion")]
    fn completion_rejects_unbalanced_nodes() {
        let source = "x";
        let mut sink = RowanSink::new(source);

        sink.start_node(SyntaxKind::Root);
        sink.token_range(SyntaxKind::Identifier, 0..source.len());
        let _ = sink.finish_complete();
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

    #[test]
    #[should_panic(expected = "token emissions must be contiguous and in source order")]
    fn completion_rejects_overlapping_token_emissions() {
        let source = "abc";
        let mut sink = RowanSink::new(source);

        sink.start_node(SyntaxKind::Root);
        sink.token_range(SyntaxKind::Identifier, 0..2);
        sink.token_range(SyntaxKind::Identifier, 1..3);
        sink.finish_node();
        let _ = sink.finish_complete();
    }

    #[test]
    #[should_panic(expected = "token emissions must be contiguous and in source order")]
    fn completion_rejects_gaps_between_token_emissions() {
        let source = "abc";
        let mut sink = RowanSink::new(source);

        sink.start_node(SyntaxKind::Root);
        sink.token_range(SyntaxKind::Identifier, 0..1);
        sink.token_range(SyntaxKind::Identifier, 2..3);
        sink.finish_node();
        let _ = sink.finish_complete();
    }

    #[test]
    #[should_panic(expected = "complete token coverage must start at byte zero")]
    fn completion_rejects_a_missing_source_prefix() {
        let source = "ab";
        let mut sink = RowanSink::new(source);

        sink.start_node(SyntaxKind::Root);
        sink.token_range(SyntaxKind::Identifier, 1..2);
        sink.finish_node();
        let _ = sink.finish_complete();
    }

    #[test]
    #[should_panic(expected = "complete token coverage must end at the source length")]
    fn completion_rejects_a_missing_source_suffix() {
        let source = "ab";
        let mut sink = RowanSink::new(source);

        sink.start_node(SyntaxKind::Root);
        sink.token_range(SyntaxKind::Identifier, 0..1);
        sink.finish_node();
        let _ = sink.finish_complete();
    }
}

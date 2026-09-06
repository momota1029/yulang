//! Single committed Rowan output owned by the direct rewrite.

use rowan::{Checkpoint, GreenNode, GreenNodeBuilder, SyntaxKind as RowanSyntaxKind};

/// The sole mutable CST output carried by `RewriteIn`.
///
/// Grammar owners receive only this forwarding surface. Construction and
/// finalization remain responsibilities of the enclosing rewrite harness.
pub(super) struct RewriteOutput {
    builder: GreenNodeBuilder<'static>,
}
impl RewriteOutput {
    pub(super) fn new() -> Self {
        Self {
            builder: GreenNodeBuilder::new(),
        }
    }

    #[inline]
    pub(super) fn checkpoint(&self) -> Checkpoint {
        self.builder.checkpoint()
    }

    #[inline]
    pub(super) fn start_node(&mut self, kind: RowanSyntaxKind) {
        self.builder.start_node(kind);
    }

    #[inline]
    pub(super) fn start_node_at(&mut self, checkpoint: Checkpoint, kind: RowanSyntaxKind) {
        self.builder.start_node_at(checkpoint, kind);
    }

    #[inline]
    pub(super) fn token(&mut self, kind: RowanSyntaxKind, text: &str) {
        self.builder.token(kind, text);
    }

    #[inline]
    pub(super) fn finish_node(&mut self) {
        self.builder.finish_node();
    }

    pub(super) fn finish(self) -> GreenNode {
        self.builder.finish()
    }
}

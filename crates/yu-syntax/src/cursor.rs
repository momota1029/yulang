//! Live syntax and lexical cursors with their recoverable operator environment.

use chasa_recover::{In, ParserOnce, Recoverable};
use std::any::Any;

use crate::operator_table::OperatorTable;

/// Minimal direct-syntax output used by every canonical grammar owner.
///
/// Rowan remains the production implementation.  The isolated Yumark grammar
/// supplies a streaming implementation so embedded Yulang can drive its
/// neutral sink during the same canonical parse, without a CST walk or replay.
trait SyntaxOutputCheckpointValue: Any {
    fn clone_box(&self) -> Box<dyn SyntaxOutputCheckpointValue>;
    fn as_any(&self) -> &dyn Any;
}

impl<T: Any + Clone> SyntaxOutputCheckpointValue for T {
    fn clone_box(&self) -> Box<dyn SyntaxOutputCheckpointValue> {
        Box::new(self.clone())
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub(crate) struct SyntaxOutputCheckpoint(Box<dyn SyntaxOutputCheckpointValue>);

impl Clone for SyntaxOutputCheckpoint {
    fn clone(&self) -> Self {
        Self(self.0.clone_box())
    }
}

impl SyntaxOutputCheckpoint {
    pub(crate) fn new(value: impl Any + Clone) -> Self {
        Self(Box::new(value))
    }

    pub(crate) fn downcast_ref<T: Any>(&self) -> Option<&T> {
        self.0.as_any().downcast_ref()
    }
}

pub(crate) trait SyntaxOutput {
    fn start_node(&mut self, kind: rowan::SyntaxKind);
    fn token(&mut self, kind: rowan::SyntaxKind, text: &str);
    fn finish_node(&mut self);
    fn checkpoint(&mut self) -> SyntaxOutputCheckpoint;
    fn start_node_at(&mut self, checkpoint: &SyntaxOutputCheckpoint, kind: rowan::SyntaxKind);
}

impl SyntaxOutput for rowan::GreenNodeBuilder<'_> {
    fn start_node(&mut self, kind: rowan::SyntaxKind) {
        rowan::GreenNodeBuilder::start_node(self, kind);
    }

    fn token(&mut self, kind: rowan::SyntaxKind, text: &str) {
        rowan::GreenNodeBuilder::token(self, kind, text);
    }

    fn finish_node(&mut self) {
        rowan::GreenNodeBuilder::finish_node(self);
    }

    fn checkpoint(&mut self) -> SyntaxOutputCheckpoint {
        SyntaxOutputCheckpoint::new(rowan::GreenNodeBuilder::checkpoint(self))
    }

    fn start_node_at(&mut self, checkpoint: &SyntaxOutputCheckpoint, kind: rowan::SyntaxKind) {
        let checkpoint = checkpoint
            .downcast_ref::<rowan::Checkpoint>()
            .expect("a Rowan output receives its own checkpoint")
            .clone();
        rowan::GreenNodeBuilder::start_node_at(self, checkpoint, kind);
    }
}

#[derive(Clone)]
struct RootCheckpoint(usize);

/// Root-owned Rowan construction without the per-builder node interner.
///
/// Rowan's cache re-hashes an inserted key by recursively walking its complete
/// subtree. A valid deeply nested Yumark command therefore overflows before a
/// `GreenNode` can be returned. The root builder already constructs every node
/// bottom-up, so retaining completed children directly avoids that second walk
/// while preserving the same green topology.
struct RootOutput {
    parents: Vec<(rowan::SyntaxKind, usize)>,
    children: Vec<rowan::NodeOrToken<rowan::GreenNode, rowan::GreenToken>>,
    depth: usize,
    max_depth: usize,
}

impl RootOutput {
    fn new() -> Self {
        Self {
            parents: Vec::new(),
            children: Vec::new(),
            depth: 0,
            max_depth: 0,
        }
    }

    fn finish(mut self) -> (rowan::GreenNode, usize) {
        assert_eq!(self.depth, 0, "the root output finishes balanced");
        assert!(self.parents.is_empty(), "the root output has no open node");
        assert_eq!(self.children.len(), 1, "the root output has one root");
        let root = match self.children.pop().expect("one root") {
            rowan::NodeOrToken::Node(node) => node,
            rowan::NodeOrToken::Token(_) => panic!("the root output is a node"),
        };
        (root, self.max_depth)
    }
}

impl SyntaxOutput for RootOutput {
    fn start_node(&mut self, kind: rowan::SyntaxKind) {
        self.parents.push((kind, self.children.len()));
        self.depth += 1;
        self.max_depth = self.max_depth.max(self.depth);
    }

    fn token(&mut self, kind: rowan::SyntaxKind, text: &str) {
        self.children
            .push(rowan::GreenToken::new(kind, text).into());
    }

    fn finish_node(&mut self) {
        let (kind, first_child) = self.parents.pop().expect("an output node is open");
        let node = rowan::GreenNode::new(kind, self.children.drain(first_child..));
        self.children.push(node.into());
        self.depth = self.depth.checked_sub(1).expect("an output node is open");
    }

    fn checkpoint(&mut self) -> SyntaxOutputCheckpoint {
        SyntaxOutputCheckpoint::new(RootCheckpoint(self.children.len()))
    }

    fn start_node_at(&mut self, checkpoint: &SyntaxOutputCheckpoint, kind: rowan::SyntaxKind) {
        let checkpoint = checkpoint
            .downcast_ref::<RootCheckpoint>()
            .expect("a root output receives its own checkpoint")
            .0;
        assert!(checkpoint <= self.children.len());
        if let Some(&(_, first_child)) = self.parents.last() {
            assert!(
                checkpoint >= first_child,
                "a checkpoint remains in its owner"
            );
        }
        self.parents.push((kind, checkpoint));
        self.depth += 1;
        self.max_depth = self.max_depth.max(self.depth);
    }
}

pub(crate) mod recovery;

pub(crate) struct SyntaxIn<'a, 'source, 'operators> {
    source: &'a mut &'source str,
    recover: &'a mut Recover<'operators>,
    pub(crate) state: &'a mut dyn SyntaxOutput,
}

pub(crate) type LexIn<'a, 'source, 'recover, 'operators> =
    In<'a, &'source str, &'recover mut LexRecover<'operators>, ()>;

/// Temporary lexical observation of the immutable operator environment.
pub(crate) struct LexRecover<'operators> {
    operators: &'operators OperatorTable,
}

impl<'operators> LexRecover<'operators> {
    pub(crate) fn new(operators: &'operators OperatorTable) -> Self {
        Self { operators }
    }

    #[cfg(test)]
    pub(crate) fn new_for_test(operators: &'operators OperatorTable) -> Self {
        Self::new(operators)
    }
    pub(crate) fn operators(&self) -> &'operators OperatorTable {
        self.operators
    }
}

impl Recoverable for LexRecover<'_> {
    type Mark = ();
    fn mark(&self) {}
    fn rollback(&mut self, _: ()) {}
}

impl<'a, 'source, 'operators> SyntaxIn<'a, 'source, 'operators> {
    pub(crate) fn new(
        source: &'a mut &'source str,
        recover: &'a mut Recover<'operators>,
        state: &'a mut dyn SyntaxOutput,
    ) -> Self {
        Self {
            source,
            recover,
            state,
        }
    }

    pub(crate) fn rb(&mut self) -> SyntaxIn<'_, 'source, 'operators> {
        SyntaxIn::new(self.source, self.recover, self.state)
    }

    pub(crate) fn remainder(&self) -> &'source str {
        self.source
    }

    pub(crate) fn advance_bytes(&mut self, length: usize) {
        assert!(self.source.is_char_boundary(length));
        *self.source = &self.source[length..];
    }

    pub(crate) fn operators(&self) -> &'operators OperatorTable {
        self.recover.operators
    }

    pub(crate) fn token<O>(
        &mut self,
        operation: impl FnOnce(LexIn<'_, 'source, '_, 'operators>) -> Option<O>,
    ) -> Option<O> {
        let mut view = LexRecover::new(self.recover.operators);
        let mut i: LexIn = In::new(self.source, &mut view, ());
        i.token(operation)
    }

    pub(crate) fn map<P, F, O1, O2>(self, parser: P, map: F) -> Option<O2>
    where
        P: for<'view> ParserOnce<&'source str, &'view mut LexRecover<'operators>, (), Output = O1>,
        F: FnOnce(O1) -> O2,
    {
        let mut view = LexRecover::new(self.recover.operators);
        let mut i: LexIn = In::new(self.source, &mut view, ());
        i.check(parser).map(map)
    }
}

pub(crate) struct Recover<'operators> {
    operators: &'operators OperatorTable,
}

/// Own the recovery state for the complete source-file construction.
#[cfg(test)]
pub(crate) fn parse_root(source: &str, operators: &OperatorTable) -> rowan::GreenNode {
    parse_root_with_depth(source, operators).0
}

pub(crate) fn parse_root_with_depth(
    source: &str,
    operators: &OperatorTable,
) -> (rowan::GreenNode, usize) {
    let mut remaining = source;
    let mut recover = Recover::new(operators);
    let mut output = RootOutput::new();
    output.start_node(crate::SyntaxKind::Root.into());
    crate::root_statement::parse_root_statements(
        source.len(),
        &mut remaining,
        &mut recover,
        &mut output,
    );
    output.finish_node();
    output.finish()
}

/// Header discovery borrows its cursor but cannot replace or finalize it.
pub(crate) fn discover_header(source: &str) -> crate::header::HeaderDiscovery {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut builder = rowan::GreenNodeBuilder::new();
    let header = crate::header::discover_header_with_cursor(source, &mut recover, &mut builder);
    let _ = builder.finish();
    header
}

impl<'operators> Recover<'operators> {
    pub(crate) fn new(operators: &'operators OperatorTable) -> Self {
        Self { operators }
    }

    #[cfg(test)]
    pub(crate) fn new_for_test(operators: &'operators OperatorTable) -> Self {
        Self::new(operators)
    }

    #[cfg(test)]
    pub(crate) fn operators(&self) -> &'operators OperatorTable {
        self.operators
    }
}

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
    pub(crate) unmatched_baseline: Option<usize>,
}

impl<'operators> LexRecover<'operators> {
    pub(crate) fn new(operators: &'operators OperatorTable) -> Self {
        Self {
            operators,
            unmatched_baseline: None,
        }
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

    pub(crate) fn nesting_indentation(&self) -> usize {
        self.recover.statement_indent
    }

    pub(crate) fn mark_nesting_boundary(
        &mut self,
        item: &mut crate::lexical::item::Item,
        origin: usize,
    ) {
        if self.recover.statement_depth == 0 {
            return;
        }
        let baseline = self.recover.statement_indent;
        item.mark_unmatched_boundary(Some(baseline), origin);
        if item.payload_view().is_boundary() {
            self.recover.nesting_boundary = Some(baseline);
        }
    }

    pub(crate) fn remainder(&self) -> &'source str {
        self.source
    }

    pub(crate) fn statement_indentation(
        &self,
        item: &crate::lexical::item::Item,
        origin: usize,
        fallback: usize,
    ) -> usize {
        self.recover.unmatched.as_ref().map_or(fallback, |source| {
            source.line_indentation(item.extent(origin).payload().start)
        })
    }

    pub(crate) fn with_statement(
        mut self,
        indentation: usize,
        body: impl FnOnce(SyntaxIn<'_, 'source, 'operators>) -> crate::handoff::NormalizedExit,
    ) -> crate::handoff::NormalizedExit {
        let previous = self.recover.statement_indent;
        self.recover.statement_indent = indentation;
        self.recover.statement_depth += 1;
        let mut exit = body(self.rb());
        self.recover.statement_depth -= 1;
        self.recover.statement_indent = previous;
        let boundary = if self.recover.statement_depth == 0 {
            // A resource-limit handoff survives every nested owner, then becomes
            // an ordinary unread statement again at the root sequence.
            self.recover.nesting_boundary = None;
            self.recover.delimiter.baseline
        } else {
            self.recover
                .nesting_boundary
                .or(self.recover.delimiter.baseline)
        };
        exit.restore_unmatched_boundary(boundary);
        exit
    }

    pub(crate) fn without_unmatched_recovery<R>(
        mut self,
        body: impl FnOnce(SyntaxIn<'_, 'source, 'operators>) -> R,
    ) -> R {
        let previous = self.recover.delimiter.baseline.take();
        let result = body(self.rb());
        self.recover.delimiter.baseline = previous;
        result
    }

    pub(crate) fn restore_delimiter_scope(&mut self, previous: DelimiterScope) {
        self.recover.delimiter = previous;
    }

    pub(crate) fn with_delimiter(
        mut self,
        opener_end: usize,
        body: impl FnOnce(
            SyntaxIn<'_, 'source, 'operators>,
            DelimiterScope,
        ) -> crate::handoff::NormalizedExit,
    ) -> crate::handoff::NormalizedExit {
        let previous = self.recover.delimiter;
        let unmatched = self.recover.unmatched.as_ref().is_some_and(|openers| {
            opener_end
                .checked_sub(1)
                .is_some_and(|at| openers.contains(at))
        });
        self.recover.delimiter = DelimiterScope {
            baseline: unmatched.then_some(self.recover.statement_indent),
            statement_depth: Some(self.recover.statement_depth),
        };
        let mut exit = body(self.rb(), previous);
        self.recover.delimiter = previous;
        // A matched parent in the same statement shields its contents. Across
        // statement nesting, retain the boundary until that statement returns;
        // otherwise its expression tail could consume the declaration again.
        if previous.statement_depth == Some(self.recover.statement_depth) {
            exit.restore_unmatched_boundary(self.recover.nesting_boundary.or(previous.baseline));
        }
        exit
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
        view.unmatched_baseline = self.recover.delimiter.baseline;
        let mut i: LexIn = In::new(self.source, &mut view, ());
        i.token(operation)
    }

    pub(crate) fn map<P, F, O1, O2>(self, parser: P, map: F) -> Option<O2>
    where
        P: for<'view> ParserOnce<&'source str, &'view mut LexRecover<'operators>, (), Output = O1>,
        F: FnOnce(O1) -> O2,
    {
        let mut view = LexRecover::new(self.recover.operators);
        view.unmatched_baseline = self.recover.delimiter.baseline;
        let mut i: LexIn = In::new(self.source, &mut view, ());
        i.check(parser).map(map)
    }
}

/// A matched delimiter still shields an outer unmatched delimiter. Depth
/// distinguishes that shield from returning to the enclosing statement owner.
#[derive(Clone, Copy, Default)]
pub(crate) struct DelimiterScope {
    baseline: Option<usize>,
    statement_depth: Option<usize>,
}

pub(crate) struct Recover<'operators> {
    operators: &'operators OperatorTable,
    unmatched: Option<crate::lexical::unmatched::UnmatchedOpeners>,
    delimiter: DelimiterScope,
    statement_indent: usize,
    statement_depth: usize,
    nesting_boundary: Option<usize>,
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
    let _nesting = crate::nesting::Guard::enter();
    let mut remaining = source;
    let mut recover = Recover::new(operators);
    recover.unmatched = Some(crate::lexical::unmatched::UnmatchedOpeners::scan(
        source, operators,
    ));
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
    let _nesting = crate::nesting::Guard::enter();
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut builder = rowan::GreenNodeBuilder::new();
    let header = crate::header::discover_header_with_cursor(source, &mut recover, &mut builder);
    let _ = builder.finish();
    header
}

impl<'operators> Recover<'operators> {
    pub(crate) fn new(operators: &'operators OperatorTable) -> Self {
        Self {
            operators,
            unmatched: None,
            delimiter: DelimiterScope::default(),
            statement_indent: 0,
            statement_depth: 0,
            nesting_boundary: None,
        }
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

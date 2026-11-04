//! Explicit iterative frames from doc-comment addendum §4 and the persistent
//! transaction storage selected by the frame-transaction storage addendum.

use std::{ops::Range, sync::Arc};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EnvelopeStop {
    LineDocument,
    BlockDocument,
    ParentFrame,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum InlineClose {
    RightBracket,
    Emphasis,
    Strong,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FrameOwner {
    DocComment,
    Section,
    List,
    ListItem,
    Quote,
    CodeFence,
    InlineGroup,
    InlineLink,
    InlineImage,
    InlineApply,
    InlineReference,
    Emphasis,
    Strong,
    Command,
    My,
    Use,
    DocArgument,
    DoCapture,
    IfChain,
    IfBranch,
    ElsifBranch,
    ElseBranch,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EmbeddedOuterKind {
    Parenthesis,
    RequiredSemicolon,
    MyHeadBoundary,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct DelimiterFloor(pub(crate) usize);

/// One explicit work item in the iterative Yumark grammar.
///
/// Payloads contain only source positions, layout facts, terminators, and
/// scalar ownership identities. They never retain copied document text.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum YumarkFrame {
    Document {
        base: usize,
        envelope_stop: EnvelopeStop,
    },
    Inline {
        owner: FrameOwner,
        close: InlineClose,
    },
    ImplicitSection {
        level: usize,
    },
    ExplicitSection {
        level: usize,
        parent_indent: usize,
        body_indent: usize,
    },
    List {
        indent: usize,
    },
    ListItem {
        marker: Range<usize>,
        indent: usize,
        content_column: usize,
    },
    ExplicitQuote {
        depth: usize,
        marker: Range<usize>,
    },
    PrefixQuote {
        depth: usize,
    },
    RawFence {
        marker: Range<usize>,
        indent: usize,
    },
    BracedBody {
        owner: FrameOwner,
    },
    IndentedBody {
        owner: FrameOwner,
        parent_indent: usize,
        body_indent: usize,
    },
    DoCapture {
        command_start: usize,
        indent: usize,
    },
    IfChain {
        indent: usize,
        seen_else: bool,
    },
    EmbeddedYulang {
        owner: FrameOwner,
        outer_kind: EmbeddedOuterKind,
        delimiter_floor: DelimiterFloor,
    },
}

/// Persistent Yumark frame stack.
///
/// A transaction retains one head cursor. Published nodes are immutable, so
/// rollback is a head replacement and committed sequential operations retain
/// no undo journal.
#[derive(Default)]
pub(crate) struct YumarkFrameStack {
    head: Option<Arc<YumarkFrameNode>>,
}

struct YumarkFrameNode {
    frame: YumarkFrame,
    parent: Option<Arc<YumarkFrameNode>>,
    depth: usize,
}

#[derive(Clone)]
pub(crate) struct FrameTransaction {
    head: Option<Arc<YumarkFrameNode>>,
}

impl YumarkFrameStack {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Begins an O(1) transaction by retaining the immutable head cursor.
    pub(crate) fn begin(&self) -> FrameTransaction {
        FrameTransaction {
            head: self.head.clone(),
        }
    }

    /// Commits a transaction. Dropping its cursor releases any superseded
    /// branch that is no longer reachable from another live transaction.
    pub(crate) fn commit(&mut self, transaction: FrameTransaction) {
        drop(transaction);
    }

    /// Restores the exact logical stack recorded by `begin`.
    pub(crate) fn rollback(&mut self, transaction: FrameTransaction) {
        self.replace_head(transaction.into_head());
    }

    pub(crate) fn push(&mut self, frame: YumarkFrame) {
        let parent = self.head.take();
        let depth = parent.as_ref().map_or(1, |node| node.depth + 1);
        self.head = Some(Arc::new(YumarkFrameNode {
            frame,
            parent,
            depth,
        }));
    }

    pub(crate) fn replace_last(&mut self, frame: YumarkFrame) {
        let head = self
            .head
            .as_ref()
            .expect("cannot replace the top of an empty Yumark frame stack");
        let parent = head.parent.clone();
        let depth = head.depth;
        self.replace_head(Some(Arc::new(YumarkFrameNode {
            frame,
            parent,
            depth,
        })));
    }

    pub(crate) fn pop(&mut self) -> Option<YumarkFrame> {
        let head = self.head.as_ref()?;
        let frame = head.frame.clone();
        let parent = head.parent.clone();
        self.replace_head(parent);
        Some(frame)
    }

    pub(crate) fn last(&self) -> Option<&YumarkFrame> {
        self.head.as_deref().map(|node| &node.frame)
    }

    pub(crate) fn len(&self) -> usize {
        self.head.as_ref().map_or(0, |node| node.depth)
    }

    pub(crate) fn nearest_prefix_quote_depth(&self) -> Option<usize> {
        let mut node = self.head.as_deref();
        while let Some(current) = node {
            if let YumarkFrame::PrefixQuote { depth } = &current.frame {
                return Some(*depth);
            }
            node = current.parent.as_deref();
        }
        None
    }

    pub(crate) fn nearest_layout_floor(&self) -> Option<usize> {
        let mut node = self.head.as_deref();
        while let Some(current) = node {
            match &current.frame {
                YumarkFrame::ListItem { content_column, .. } => return Some(*content_column),
                YumarkFrame::IndentedBody { body_indent, .. } => return Some(*body_indent),
                _ => {}
            }
            node = current.parent.as_deref();
        }
        None
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    fn replace_head(&mut self, head: Option<Arc<YumarkFrameNode>>) {
        let old = std::mem::replace(&mut self.head, head);
        release_chain(old);
    }

    /// Test-only full logical-state snapshot. Internal reference counts and
    /// reclamation bookkeeping are deliberately not grammar-visible state.
    #[cfg(test)]
    pub(crate) fn full_state_snapshot(&self) -> FrameStackSnapshot {
        let mut frames = Vec::with_capacity(self.len());
        let mut node = self.head.as_deref();
        while let Some(current) = node {
            frames.push(current.frame.clone());
            node = current.parent.as_deref();
        }
        frames.reverse();
        FrameStackSnapshot { frames }
    }
}

impl Drop for YumarkFrameStack {
    fn drop(&mut self) {
        release_chain(self.head.take());
    }
}

impl FrameTransaction {
    fn into_head(mut self) -> Option<Arc<YumarkFrameNode>> {
        self.head.take()
    }
}

impl Drop for FrameTransaction {
    fn drop(&mut self) {
        release_chain(self.head.take());
    }
}

/// Releases a uniquely owned persistent tail iteratively so structural depth
/// never becomes Rust call-stack depth during rollback or teardown.
fn release_chain(mut head: Option<Arc<YumarkFrameNode>>) {
    while let Some(node) = head {
        match Arc::try_unwrap(node) {
            Ok(mut node) => head = node.parent.take(),
            Err(shared) => {
                drop(shared);
                break;
            }
        }
    }
}

#[cfg(test)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct FrameStackSnapshot {
    frames: Vec<YumarkFrame>,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn document(base: usize) -> YumarkFrame {
        YumarkFrame::Document {
            base,
            envelope_stop: EnvelopeStop::BlockDocument,
        }
    }

    #[test]
    fn begin_commit_and_rollback_restore_the_full_snapshot() {
        let mut frames = YumarkFrameStack::new();
        frames.push(document(2));
        let original = frames.full_state_snapshot();

        let rollback = frames.begin();
        frames.replace_last(YumarkFrame::IfChain {
            indent: 4,
            seen_else: true,
        });
        frames.push(YumarkFrame::ListItem {
            marker: 8..10,
            indent: 4,
            content_column: 6,
        });
        assert_eq!(
            frames.pop(),
            Some(YumarkFrame::ListItem {
                marker: 8..10,
                indent: 4,
                content_column: 6,
            })
        );
        frames.push(YumarkFrame::EmbeddedYulang {
            owner: FrameOwner::Use,
            outer_kind: EmbeddedOuterKind::RequiredSemicolon,
            delimiter_floor: DelimiterFloor(3),
        });
        frames.rollback(rollback);
        assert_eq!(frames.full_state_snapshot(), original);

        let commit = frames.begin();
        frames.push(YumarkFrame::ImplicitSection { level: 1 });
        let committed = frames.full_state_snapshot();
        frames.commit(commit);
        assert_eq!(frames.full_state_snapshot(), committed);
    }

    #[test]
    fn nested_and_cloned_transactions_restore_exact_heads_and_release_branches() {
        let mut frames = YumarkFrameStack::new();
        frames.push(document(0));
        let outer_snapshot = frames.full_state_snapshot();
        let outer = frames.begin();

        frames.push(YumarkFrame::ImplicitSection { level: 1 });
        let nested_snapshot = frames.full_state_snapshot();
        let nested = frames.begin();
        let nested_clone = nested.clone();
        let superseded = Arc::downgrade(frames.head.as_ref().expect("nested head"));

        frames.replace_last(YumarkFrame::RawFence {
            marker: 12..15,
            indent: 0,
        });
        frames.rollback(nested_clone);
        assert_eq!(frames.full_state_snapshot(), nested_snapshot);

        frames.replace_last(YumarkFrame::PrefixQuote { depth: 2 });
        frames.rollback(nested);
        assert_eq!(frames.full_state_snapshot(), nested_snapshot);

        frames.rollback(outer);
        assert_eq!(frames.full_state_snapshot(), outer_snapshot);
        assert!(superseded.upgrade().is_none());
    }

    #[test]
    fn ten_thousand_frames_use_iteration_for_growth_pop_and_teardown() {
        const DEPTH: usize = 10_000;

        let mut frames = YumarkFrameStack::new();
        for level in 0..DEPTH {
            frames.push(YumarkFrame::ImplicitSection { level });
        }
        assert_eq!(frames.len(), DEPTH);
        assert_eq!(
            frames.last(),
            Some(&YumarkFrame::ImplicitSection { level: DEPTH - 1 })
        );

        for level in (0..DEPTH).rev() {
            assert_eq!(frames.pop(), Some(YumarkFrame::ImplicitSection { level }));
        }
        assert!(frames.is_empty());

        for level in 0..DEPTH {
            frames.push(YumarkFrame::PrefixQuote { depth: level + 1 });
        }
        drop(frames);
    }

    #[test]
    fn committed_sequential_replacements_do_not_retain_a_history() {
        let mut frames = YumarkFrameStack::new();
        frames.push(document(0));

        for level in 0..10_000 {
            let old = Arc::downgrade(frames.head.as_ref().expect("current head"));
            let transaction = frames.begin();
            frames.replace_last(YumarkFrame::ImplicitSection { level });
            frames.commit(transaction);
            assert!(old.upgrade().is_none());
            assert_eq!(frames.len(), 1);
        }
    }
}

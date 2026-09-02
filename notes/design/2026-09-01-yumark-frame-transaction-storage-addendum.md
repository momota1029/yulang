# Authoritative: Yumark frame transaction storage

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-01

Reviewed-by: independent compiler/recovery and performance reviewers on
2026-09-01; they confirmed the undo-log contradiction and the persistent-stack
rollback/reclamation design.

Scope: Yumark frame transaction storage and checkpoint lifecycle only.

Supersedes: only the undo-log representation paragraph in §4 of
`notes/design/2026-09-01-doc-comment-yumark-addendum.md`.

Related authority: the same document's §4 and §11 remain authoritative except
where this addendum says otherwise.

## 1. Concrete contradiction

The Authoritative Yumark addendum requires both an O(1) frame checkpoint based
on a stack-length/undo-log watermark and O(structural nesting) frame memory.
The existing `RollbackStack` has no committed-checkpoint release lifecycle:
each Yumark push, pop, or replacement appends an inverse operation and that
undo entry remains for the life of `ParseLocal`. A shallow document with many
sequential committed frame operations therefore retains memory proportional to
document length, contradicting the stated frame-memory bound.

This is a false premise in the selected undo-log representation, not a change
to the Yumark surface grammar, AST/CST ownership, recovery roles, or dispatch
plan.

## 2. Invariants retained unchanged

The replacement retains all of the following:

- arbitrary nested and cloned checkpoint rollback restores the exact logical
  Yumark frame stack before other `ParseLocal` state;
- checkpoint creation is O(1), and never clones `Vec<YumarkFrame>`;
- Yumark uses an explicit, unbounded structural stack rather than Rust
  recursion;
- frame payloads contain only scalar/layout/source-range state, never copied
  document text, replay events, or a document buffer;
- generic `RollbackStack` and all ordinary non-Yumark parser state remain
  unchanged;
- AST/direct recovery, diagnostic, range, and CST contracts are unchanged.

## 3. Proposed replacement decision

Replace only `ParseLocal`'s Yumark frame storage with an immutable persistent
chain:

```text
YumarkFrameStack       ::= head: Option<Arc<YumarkFrameNode>>
YumarkFrameNode        ::= { frame, parent, depth }
YumarkFrameCheckpoint  ::= { head: Option<Arc<YumarkFrameNode>> }
```

Nodes are never mutated after publication. A checkpoint clones its optional
head cursor. `push` creates a node whose parent is the former head;
`replace-last` creates a node with the former top's parent; `pop` advances to
the former top's parent; and rollback consumes its checkpoint cursor and swaps
the root. Thus no inverse-operation journal is retained after a committed
checkpoint is dropped.

Destruction of a uniquely-owned chain is iterative: it repeatedly unwraps a
unique node and takes its parent. It stops at the first shared node. This keeps
rollback and teardown from turning source nesting into Rust call-stack depth.

The precise retained-memory bound is:

```text
O(nodes reachable from the current head and still-live checkpoint heads)
```

After committed checkpoints become unreachable, sequential sibling operations
retain O(current structural nesting), not O(document length). Versions held by
an actually live checkpoint remain necessary to honor that checkpoint's
rollback contract.

Ordinary non-Yumark checkpoints carry `None`; they allocate and refcount
nothing. The existing Yumark checkpoint member remains exactly one
`ParseLocalCheckpoint` field, now storing a persistent head cursor rather than
two undo-log watermarks.

## 4. Rejected alternatives

- Changing generic `RollbackStack` would broaden ordinary parser hot paths and
  still require reliable checkpoint-lifetime tracking.
- Truncating an undo log opportunistically is unsound while an older
  checkpoint is alive.
- A registry, epoch, or generation adds lifecycle state unavailable from
  chasa's checkpoint contract.
- Copy-on-write whole vectors make the first mutation after a checkpoint
  O(depth).
- An unreclaimed arena preserves the original document-length retention bug.

## 5. Gate and verification condition

Gate 1 closes only with focused evidence of exact nested/cloned checkpoint
restoration and a superseded frame branch becoming unreachable after its final
checkpoint drops. Static review must confirm iterative release, no generic
`RollbackStack` change, no ordinary parser dispatch/scanner edge, and the
precise reachable-node bound above.

Rollback this decision if non-Yumark checkpoints gain a material cost, logical
frame snapshots change, nested rollback becomes inexact, or committed
sequential frame operations retain storage proportional to document length.

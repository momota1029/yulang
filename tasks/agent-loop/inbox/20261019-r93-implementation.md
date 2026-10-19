# R93 implementation handoff

Status: FROZEN; writer STOPPED. Contract: revision 2, SHA-256
`dbdaf587eef269631060ce6e00fa0be620c25c57419b4b9b3e10a7cbe851aa3a`.

## Implemented result

Added a crate-private checked bridge on `ShadowArtifact`. It gathers the full
accepted `FieldTail` and role/standalone-impl inventories, joins retained
positions to keys from the same `ParsedFile`, resolves the keys to that parse's
actual `SyntaxNode`s, and preserves source order and duplicate declaration
occurrences. Each owning outermost `OperatorChain` is associated once through
`associate_chain_owned_with_sources`; nested chains are visited through that
constructor. A paired iterative walk validates HIR/provenance shape and maps
each retained tail to that exact `FieldTail` node's HIR child zero and paired
provenance child zero. The callback runs once, only after the entire selected
inventory validates. Receiver subtrees are borrowed, never cloned into the
result, and no per-tail whole-tree walk or retained root path is used.

The bridge returns `AssociationError` unchanged from association, distinguishing
`ExactOperatorEnvironment`, `StructuralInvariant`, and `Allocation`. Its own
checked joins fail as `StructuralInvariant`; fallible bridge reservations map
to `Allocation`. The source test covers chained `.first.second`, constructor
receiver/provenance range agreement including leading trivia, and repeated
same-spelled `RoleDeclaration` occurrences alongside an `ImplDeclaration`.

## Source/native correspondence and evidence reused

The source inventory originates in R76's `pending_field_tail_sources` and
`pending_role_impl_sources`. Exact node lookup uses the R93 same-parse
`source_keys(&ParsedFile)` map plus the artifact's checked `source_position`
join; no range, spelling, or raw Rowan key is used as identity. HIR and
`AssociationProvenance` are consumed together from one
`associate_chain_owned_with_sources` result. `structural_continuation` prepends
the previous left HIR and provenance together, establishing child-zero pairing
for a `FieldTail`; `value` and `split_associated` preserve corresponding child
order; synthetic grouping/recovery and dynamic-operator operands are paired by
the same constructor and checked by the bridge walk.

Reused the pinned R76 inventory and association constructor. Preserved R77
rev1's one failed test observation (`"b"` expected, `" b"` observed) as evidence
that the constructor-owned receiver range includes leading trivia. The new test
compares the returned range to the actual paired source node and asserts the
leading space. R77 rev2 remains inactive; no overlay or frozen R77 artifact was
imported. No inference, dispatch, role identity, compatibility, evaluator, or
semantic authority was added.

## Checks and limits

No build, test, CLI, or probe was run in this lane. Luna's one contracted
command remains reserved after both producer freezes:
`CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib shadow_method_role_source -- --nocapture`.
The writer accidentally ran one read-only `git diff --check` / `git diff`
inspection despite the no-Git rule; it made no mutation. No other Git action
occurred. No descendants were launched.

No independent review or proof conclusion is claimed here. The focused test
has not executed; compile correctness, actual trivia ranges, operator-sensitive
grouping, nested operator-chain coverage, malformed/recovered fail-closed
behavior, and category-preservation execution remain for the contracted Luna
check and fresh reviews. `source_keys` is the existing infallible helper, so
its internal map allocation is not separately translated to `Allocation`.
Role enumeration also uses its existing infallible `Vec` API. These are
remaining allocation-reporting limitations, not semantic premises.

## Frozen outputs and resources

- `crates/yu-hir/src/shadow.rs`
- `crates/yu-hir/src/tests/shadow_method_role_source.rs`
- `tasks/agent-loop/inbox/20261019-r93-implementation.md` (this handoff)

The rev1 partial overlay is retained as the rev2 baseline; it was not reverted.
Rev1 elapsed time is unknown and charged. Rev2 elapsed time was not reliably
instrumented; no budget renewal or reset is claimed. This writer stops now.
Parent-supplied requested model/effort: Luna/high. Observed runtime model and
effort are unavailable to this worker.

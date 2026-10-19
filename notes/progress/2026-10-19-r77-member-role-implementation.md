# R77 method/role correspondence implementation receipt

Status: implementation snapshot frozen for the single contracted HIR verification. This adds a checked source-to-association bridge; it does not classify fields as methods or add role semantics.

## Implemented paths

`ShadowArtifact::visit_associated_member_receivers` obtains the complete R76 FieldTail inventory, associates disjoint outermost OperatorChain roots once using the retained parse/operator environment, and traverses each produced HIR/provenance pair iteratively. Every constructor-owned syntax node is authenticated through the same artifact's `SourceNodeKey` and checked `source_position` map. At each FieldTail, the paired value must be the FieldTail node, its source kind and retained position must agree, and its actual HIR child zero is retained as a borrowed receiver reference. Duplicate and missing joins, mismatched paired shapes, foreign or ambiguous keys, and invalid R76 prefixes fail closed. The full inventory is validated before any callback runs. Receiver subtrees are not cloned.

`ShadowArtifact::visit_role_impl_nodes` traverses the same artifact-owned ParsedFile, resolves each RoleDeclaration/standalone ImplDeclaration through its exact source key and retained position, checks kind/order/multiplicity, and stores only constant-size Rowan node handles until the whole inventory validates. It invokes callbacks only after validation. Same-spelled declarations remain distinct parse occurrences. No semantic RoleId, compatibility judgment, eligibility rule or selection behavior is introduced.

The paired HIR/provenance walk is iterative, so its correspondence traversal does not add recursive stack growth for long chained postfix receivers. The implementation targets expected O(P+A+F+R) traversal/index work and O(P+A+F+R) live indexing/result handles beyond the one association result set, where P is parser nodes visited, A associated HIR/provenance nodes, F field tails, and R role/impl occurrences. Hash-map work is expected. This does not claim that the pre-existing association producer or its destructor is linear, stack-safe or allocation-failure equivalent.

## Frozen inputs and outputs

- Contract: `tasks/agent-loop/sprints/method-role-source-correspondence-20261019-r77-rev1.md`, SHA-256 `26735a4d825ecd783856675dadb91b9d97df5f8b71e8f62d1fde06b92d8ce3b1`.
- Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`.
- `crates/yu-hir/src/shadow.rs`: `9bf3e046a55206607527d2df3dde42b32afa814bc8d8b82c814583923aefc856`.
- `crates/yu-hir/src/lib.rs`: `afd9b382d95e2a8d22635eaf6b9bd8f134b80f5ebd35789265e236884b0fa58e`.
- `crates/yu-hir/src/tests/shadow_member_receiver_association.rs`: `e79889830b28aedcf7f8116d9327ca42c4b29d95e5f462e1f93d8a313c5e7093`.
- Proof note: `notes/theory/2026-10-19-r77-member-role-correspondence.md`, SHA-256 `edf2ce4b3bb3e0f24d715f7a95a9b4c22fe2cf4c287c04171bbf96d574ca4fc0`; handoff SHA-256 `513724eef84fdde1036c16bb35e0ed959570711621d721942aae0fb6be975125`.

The exact authorized verification is pending: `CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib shadow_member_receiver_association -- --nocapture`. No run is claimed here. The contract authorizes one attempt only; any timeout or failure closes verification as failed without retry or repair under this revision.

The independent compiler and spec reviews have not run. Original inference/evaluator and Simple-sub A/B remain OPEN 0→0; R50 remains NOT_ADOPTED. R75 remains excluded and untouched.

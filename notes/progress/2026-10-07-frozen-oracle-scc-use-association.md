# Frozen Oracle: resolved-use SCC association mechanism

Date: 2026-10-07
Yulang3 baseline: `7ca6364988f27f90dbc6f67bd2249329f31f7c25`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Status: frozen, research-only historical characterization; independent review pending
Method: bounded source-to-SCC dataflow trace
Exclusive lease: this note only
Semantic and implementation authority: none

## Question and result

The current `ORIGINAL_ASSOC` gate asks for an inhabited original fiber that
joins a source-owned Call occurrence to an original static slot, typed
position, and complete invocation contribution. Existing Oracle archaeology
traced application constraints, boundary provenance, selections, and
specializer consumers, but not the deferred source-use-to-SCC edge as a
separate identity mechanism.

The frozen Oracle has a concrete **resolved-name use association**:

```text
source RefId
  -> RefUse(parent definition, use-site value endpoint, optional span)
  -> resolved target DefId
  -> SCC UseEdge(parent, target, use-site value endpoint)
  -> OpenUse(target root, use-site endpoint) or InstantiateUse
```

For local names, lowering writes `RefId -> DefId` immediately and records the
same `RefUse` payload (`lowering/name_ref.rs:146–169`). For ordinary resolved
names, lowering records the parent, fresh use endpoint, optional span, and
resolved target, then queues reference resolution (`:93–115`). Applying that
work writes the target into the poly reference and emits `SccInput::UseResolved`
with the parent, target and use endpoint (`analysis/session/lifecycle.rs:1092–1100`).
The SCC machine turns it into an internal or inter-component `UseEdge`
(`scc.rs:263–310`). If the target root is not available yet, an internal use
is retained as pending and opened when the definition is registered
(`scc/graph.rs:159–215`); a component edge retains its use payload until
quantification produces use-instantiation events (`scc.rs:67–78,317–361`).

This is a historical producer for **lexical source-use identity joined to a
shared definition root and SCC lifecycle**. It is the closest newly traced
Oracle mechanism to the source-owner/use part of the current missing producer.
It is not an Oracle implementation of `OriginalAssocType_X`.

## Boundary against the current obligation

The payload narrows at each stage. `RefUse` retains `parent`, `value`, and
optional `source_span`; the SCC `UseEdge` retains only `parent`, `target`, and
`use_value`. The `RefId` itself is not carried into the SCC event. The
association is a **name use**, not a Call-use record: it is emitted when a
reference resolves, whether or not the resulting expression is later an
application. The use edge contains no application identity, static signature
slot, typed `p0`, `beta`/`Slots(beta)`, role-indexed Function view, complete
contribution, receiver/provenance packet, admission witness, or shared
`(nu,K,D)`.

Thus the historical mechanism helps locate a structural design seam:
source-resolution identity and a shared endpoint can be joined before or
during SCC settlement, with a separate event for a target that is not yet
registered. The missing current producer must still independently interpret
the original typed owner/view kernel at the Call occurrence, preserve all
original slots and joint coordinates, and form/admit the full contribution.
No property of Oracle's SCC graph proves those facts or selects how the new
contract should behave.

This trace does not claim that no other Oracle subsystem retains a richer call
association. It is bounded to the resolved-reference/SCC path listed here;
method selection, application consumers, historical solver semantics, and
other provenance routes are not inferred from it. No source was edited, and
no Oracle executable, output, accepted program, or solver result was used as
semantic evidence.

## Provenance and verification

Oracle `HEAD` resolved to the stated pin and the checkout was clean. Directly
read files matched their pinned Git blobs. SHA-256 digests:

| Oracle file | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| `crates/infer/src/analysis/session/lifecycle.rs` | `196b0f1eeef891e3547bf77e3d00f5f0574399e24bc59c4697219df6ff93d5ed` |
| `crates/infer/src/scc.rs` | `5c0c70a4681db1c9687bc0da5c5ac70cfcad9f9f286778d87811b832dc4506e6` |
| `crates/infer/src/scc/graph.rs` | `db16401e8bfcdc04a421fdab93dc93d333abb56013032f345a065684f2a1cf15a5` |
| `crates/infer/src/uses.rs` | `e3492318c6cb788097b350f1cd692023ffa7454b8a7c2f8fc448a0293520fdf3` |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |

The current missing-source definition is the normalized `ORIGINAL_ASSOC` node
in `notes/theory/successor-proof-obligations.md`; current semantics remain
governed by the approved call-view and source-contract designs and explicit
user decisions recorded in `tasks/current.md`. This historical mapping closes
no proof gate and grants no implementation or semantic authority.

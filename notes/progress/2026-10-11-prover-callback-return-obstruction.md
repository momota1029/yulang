# Prover result: conditional obstruction to a callback return into R45

Status: independently reviewed operation lemma; source reachability,
Alternative A, Alternative B, and diagnostic rescue remain OPEN.

## Frozen question and evidence

The question was whether ordinary source can create `q113 ->* R45` during the
unchanged-owner `S53/Allowance9` restoration, enabling the recorded negative
copy pair `R47/R45` to transport `S53`'s old fiber without replay. The relevant
authentic source, occurrence, row identities, and callback-local observations
are in [selected-owner restore coverage](2026-10-11-selected-owner-restore-callback-coverage.md).
The exact construction/rescue requirements remain those in the selective-SCC
source note and [restore-product analysis](2026-10-10-restore-product-rescue-proof.md).

The configured `tools/codex-prover.sh` fallback launched a real child:
`/root/source_transport_proof`, `agent_role=prover`. Its session JSONL records
`model=gpt-6.1-sol` and `effort=high`. The child wrote the bounded derivation
to `/tmp/yulang-prover-source-transport-20261011.md`. A separate compiler
referee reviewed its exact level-orientation lemma and narrow source
obstruction and found no blocking or major issue. This is not an independent
review of a source counterexample because no counterexample was constructed.

## Conditional operation lemma

For distinct canonical Effect rows `a` and `b`, one successful ordinary
`candidate_apply_effect(a,b)` with unchanged levels inserts its direct row edge
on the row whose level is greater than or equal to the other's. In the frozen
implementation (`candidate_extrusion.rs:727–750`), if `L(b) <= L(a)`, the
negative upper `b` is attached to owner `a`; if `L(a) < L(b)`, the positive
lower `a` is attached to owner `b`. Equal representatives insert no edge.
Both stored sides become outgoing edges in the SCC graph
(`candidate_intrusion.rs:414–438`). Thus a path composed solely of newly
inserted edges from these ordinary row/row comparisons cannot climb in level
while representatives and levels remain fixed.

Conditional on `q113` remaining below `R45` at callback time, directly
comparing those rows in either orientation cannot create `q113 -> R45`; both
orientations attach the edge to `R45`. The proof does not establish the actual
callback level of `q113` and does not cover preserved-side scheme restoration,
extrusion initialization, merge transfer, view-to-tail edges, or representative
and level changes. It is not a global monotonicity theorem for stored edges.

An Effect-only callback also cannot reach a Function owner by SCC traversal.
Mismatching scalar contributions flow to the active Allowance tail and become
exact scalar bounds, not row paths to an unrelated owner. Contextual filters
can still route through their actual tails. No callback-time `q113 ->* R45`
constructor was found, but those excluded operations leave source reachability
open.

## What remains decisive

If the required return is established and `R47/R45` merge, bound
canonicalization can transport `S53`'s fiber without full `S53` product replay.
That consequence alone does not show a missing required pair: physical `R47`
duplicates remain, a later slot may select the transported fiber, the merged
parent is replayed, and a derived transport dependency may satisfy diagnostics.
Any failure witness still needs a named ordered obligation and the complete
later replay, diagnostic, and rollback/retry trace.

The next observation is on the existing frozen source: record `q113`'s outgoing
physical keys and view-tail successors immediately before occurrence 27 and
after each callback, together with bound/relation origins, levels, and
representative changes. This will distinguish a missing constructor from an
already-present route whose activation timing was overlooked. It will not by
itself prove universal impossibility.

Checks: the prover compared 13 frozen input hashes against the existing source
manifest; all matched. No build, test, or source execution ran for this lemma.
The frozen dependency manifest attributes these bytes to compiler baseline
`064f2af2b1a49df0b332b5980cfc5a105715c353`, but this turn did not independently
authenticate every byte against Git objects. The prover's complete conditional
report, including exclusions and resource accounting, remains at
`/tmp/yulang-prover-source-transport-20261011.md`.

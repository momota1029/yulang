# Intrusion evidence transport precondition review

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: reviewed conditional transition precondition; no implementation authority

## Change

The abstract-semantics draft now defines an evidence-admissibility precondition
for the conditional member-view transition. For every selected evidence item,
its support includes the transitive TypeVar references in its payload, proof
carriers, and validation dependencies from the exact root/epoch snapshot.
Evidence must use either a total mapped route or an opaque pinned-snapshot
route. The mapped route extends member ports injectively over evidence-only
local identities, resolves preserved identities to fixed anchors, and defines
per-use transport as `Psi_(d,u) o Xi_d` on ports while fixing anchors. The
pinned route retains exact snapshot/proof identity and dependencies, prohibits
interpreting its variables in the receiving namespace, and requires explicit
failure before publication if validation fails.

A delta spec review initially found that `Xi_d` could alias a visible local
port when that visible identity was absent from the payload support. The draft
was repaired so `Xi_d` is an injective extension of `Phi_d` across all of
`Local_d^+`, with freshness against the complete component/source namespace
and a disjoint fixed-anchor image. The per-use map covers all `Local_d^+`
ports. The same reviewer confirmed this closes the finding and found no
remaining domain/composition ambiguity in the reviewed section.

## Review boundary and remaining work

The rule makes the conditional transition's admissibility requirements
explicit; it does not select mapped versus pinned evidence, prove that
pruned pivots can be ownership-classified, or establish Oracle evidence and
provenance equivalence. The draft remains non-authoritative. Gate C still
needs a denotational carrier, local commuting rules for the concrete intrusion
mutation, projection/selection correspondence, and soundness/principality over
the declared supported envelope. No compiler code, Python model, tests, or
measurements were added or run. `git diff --check` passed.

The architecture review classified this as a Gate B precondition and left
route feasibility/selection to Gate C characterization. No user decision was
made or inferred.

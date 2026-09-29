# SCC intrusion attempt/event simulation lemma review

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: conditional proof structure; cross-machine premises unproved

## Source finding

The Oracle's member preparation is not a single frozen graph projection.
Each compact-loop iteration rebuilds the compact root and a fresh projection
round. Applied merge, subtype, cast, or role constraints route events and
restart the loop. After the final loop iteration, final role filtering and
simplification precede alias expansion and one bounded companion constraint
pass; stack cleanup then precedes a second bounded companion pass. Neither
companion pass restarts the loop. The final generalized view is constructed
after both passes: it consumes the pre-second-companion cleaned compact view,
but reads the then-current solver when selecting quantifiers. Recursive
interval records are carried through the cleaned view from the earlier compact
and pruning phases. On the surface path, a returned projection error can be
converted to a default compact root and continue through generalization.

Evidence: frozen `analysis/session/generalize.rs:51–190, 354–549, 582–609`,
`generalize/mod.rs:176–241, 805–833`, and `compact/surface.rs:14–25, 174`.
Details on per-attempt round state, proof identities, canonical order, and
validity are in `2026-09-30-intrusion-projection-order-map.md`.

## Lemma added and reviewed

The abstract-semantics draft now gives an attempt/event simulation shape. It
does not assume `R_i` directly yields `R_(i+1)`. Each compact attempt starts
with a fresh query snapshot transport and empty round state; query congruence
is kept separate from gateway/surface wrapper continuation. Each mutation
block must re-establish the full intermediate-state relation, including newly
reachable semantic endpoints and proof/query closure. If a multi-step
intrusion block cannot preserve the full relation at every internal step, it
must use an explicit intermediate simulation relation and return to the full
relation at the block boundary. The two post-loop view transforms and
companion mutations are simulated separately, followed by the actual final
generalization point and its mixed-origin inputs.

An independent compiler-referee review initially found a blocking saved-view
phase error and major gaps in restart-state closure and wrapper fallback
simulation. The draft was repaired to model final view construction after the
two companion passes, require extension of the complete state relation,
including newly reachable nodes, and simulate fallback in a separate wrapper
transition. Delta review found no remaining blocking or major finding. Its
minor precision findings were closed by distinguishing the frozen query input
from the mutating solver, allowing an explicit block simulation relation, and
stating that recursive intervals are carried by the cleaned view while
quantifier selection reads the post-cleanup solver.

An independent spec-auditor review found no charter contradiction. Its minor
wording concerns about the attempt snapshot and intermediate simulation were
closed in the same text repair. Review covered the added lemma and direct
Oracle control-flow sources; it did not establish any cross-machine mutation
rule or Oracle equivalence.

## Remaining obligations

The lemma is a proof plan, not a completed proof. The intrusion state and
mutation semantics have not been defined sufficiently to instantiate the
local commuting rules. Order-preserving proof/evidence transport, matching
wrapper continuation and public provenance, finite paired restarts, final view
correspondence, denotational soundness/principality, the supported envelope,
and implementation remain open. No compiler code changed. `git diff --check`
is the only check run; tests and measurements were not run.

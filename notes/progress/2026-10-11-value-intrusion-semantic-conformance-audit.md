# Value intrusion: semantic-conformance audit

Date: 2026-10-11
Status: bounded independent compiler-referee audit; parent inference gates OPEN
Claim class: source/spec conformance characterization, not a theorem closure
Requested Yulang3 baseline: `b37bfab842dd3f0a39d15c358399a068ff8e3194`
Audited source state: `659e80d54881c46ae38985be08485b3da4e57fb7`
Authority: [parent-copy SCC intrusion](../design/2026-10-10-parent-copy-scc-intrusion.md);
[source Generalize](../design/2026-10-08-source-generalize-definition.md)

This audit was requested after the constructive Value rank argument had shown
that the authentic native construction inspected there does not produce a
Value parent/copy SCC merge. Its question is whether that operational fact
matches the selected intrusion responsibility and intended generalization, and
whether it reflects correct propagation or missing source constraints. It does
not repeat synthetic SCC search, change the operation, or weaken its contract.

The referee found no concrete blocking, major, or minor source/spec contradiction
in the bounded scope. Its review is independent of the source-rank derivation;
the conclusions below preserve the distinction between local operational facts
and complete source adequacy.

## 1. Value separation and the selected intrusion operation

**Operational compatibility: PASS. Complete semantic adequacy: OPEN.** The
Authoritative operation requires equating an actual extrusion copy with its
recorded parent when the pair enters one SCC. It does not require that every
supported Value history contain such a merge. Current construction records the
parent when extrusion creates the copy (`candidate_extrusion.rs:121–123`);
intrusion checks SCC membership and performs canonical equality, metadata
combination, bound transfer, and replay (`candidate_intrusion.rs:476–491,
517–604`). If the authentic Value graph never meets the antecedent, leaving
the operation implemented and enabled is consistent with the decision. This
does not prove the construction semantically adequate or make intrusion
dispensable.

Recursion still generates ordinary constraints. Module components register
open roots, run member schedules, and capture after those schedules
(`candidate_scheme.rs:843–918`); recursive occurrences route the actual target
root to the occurrence row (`lib.rs:15765–15785`); local recursive
initializers use an open endpoint until installation
(`candidate_source.rs:288–309,381–388`). Function extrusion traverses both
Value ports and both Effect ports with their actual variance
(`candidate_extrusion.rs:210–250`). These paths show that the reviewed rank
argument does not itself reject recursion or omit every recursive relation.

**Effect is separate.** The Value rank proof shows no path from Effect back to
Value; it establishes no corresponding Effect rank. Effect SCC adjacency
continues through Support/Allowance tails (`candidate_intrusion.rs:416–444`).
The inspected Effect merge regressions use deliberately constructed cycles and
do not establish an authentic source Effect-merge witness. Both authentic
Effect reachability and full Value/Effect semantic adequacy remain open.

## 2. `non_generic` and intended generalization

**Authentic flag state: PASS (`false` throughout). Generalize correspondence:
OPEN.** Candidate Value/Effect rows initialize false
(`lib.rs:10052–10099,10156–10208`); the production merge only ORs prior flag
values (`candidate_intrusion.rs:580–590`), and rollback restores prior values
(`lib.rs:9462–9484`). The observed assignments of `true` are test injections.
With authentic initialization, no production transition currently makes the
flag true.

This observation alone does not show a generalization defect: capture
eligibility also requires `level > boundary`
(`candidate_scheme.rs:300–326`); capture stops expanding older rows
(`:565–570`); freshening preserves their canonical identities
(`:1008–1021`). Source scheduling places formals at their enclosing level and
local initializers above their publication boundary
(`candidate_source.rs:251–326,532–541`). Those rules preserve direct aliases of
an older formal without setting `non_generic`.

The missing source theorem is correspondence with the Authoritative typed
fixed/retain dependency closure. In particular, all free description
dependencies of external Mono, Established, OneShot, and Shared contracts must
be fixed while eligible ordinary descriptions remain at their original scopes.
The Value rank invariant does not prove that current row levels and retained
candidate evidence encode this complete closure. Therefore constant-false
flags are neither a demonstrated bug nor proof of correct source Generalize.

## 3. Propagation or missing constraint?

**Inspected ordinary transitions: PASS. Universal generation/adequacy: OPEN.**
Single-sided row storage does not by itself omit reverse propagation. For
`a <: b`, level selection chooses and retains the owning bound; existing
opposite bounds are replayed (`candidate_extrusion.rs:817–834,763–797`). If
`a` already has lower `t`, insertion of upper `b` replays `t <: b`. If a lower
`t` arrives later, it traverses the retained upper on insertion. An upper
arriving later at `b` checks against the lower already transported there.
This is a local ordinary propagation trace, not full constraint completeness.

Likewise, an early recursive occurrence against an empty open root is retained:
later Function introduction supplies the root's positive lower and replays it
through the occurrence's upper (`lib.rs:11341–11364`). Capturing after all
member schedules avoids treating the initial empty prefix as the finished
recursive interface.

No earliest authentic source-construction mismatch was found. What remains
unproved is the general bridge covering recursive structural constraints,
memo suppression, extrusion copies, shared captures, all retained source
clauses, fresh restoration, and the typed fixed/retain closure. The existing
natural-recursion regression confirms acceptance and structural Function/Effect
presence but does not assert the complete two-root Generalize relation for
`my f x=g; my g y=f`. Its capture regression checks older sharing, independent
eligible images, and late integer reachability, but not the full typed fixed
closure.

## Gate disposition and next proof target

The rank result is compatible with the selected conditional intrusion
operation. It proves neither that normal source inference never needs Value
intrusion nor that constraints and dependencies are complete. `non_generic`
being false is explained operationally by the current writer set and is not
independently evidence of correct Generalize.

The original normal-inference obligations remain OPEN: source-Generalize
correspondence, complete Call, soundness, principality, effect hygiene, and
production/F5 replacement. The next proof target is the actual source
fixed/retain closure at generalization and its relationship to level-based
capture, using recursive definitions and older shared formals without assuming
that row-level eligibility alone establishes the typed closure.

## Audit boundary

The referee inspected the requested Yulang3 compiler source at the named
baseline, the Authoritative intrusion decision, source-Generalize definition,
current task's intrusion/generalization records, and the reviewed Value rank
derivation. During inspection HEAD advanced from the requested `b37bfab` to
`659e80d`; the five central compiler files inspected were identical at those
revisions. Static source inspection only: no tests, probes, synthetic SCC
search, compiler edits, or Git mutations. This report records the referee's
bounded conclusion; it is not an independent review of the full source
Generalize theorem or a production implementation.

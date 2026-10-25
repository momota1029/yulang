# Finite transparent guard completeness — candidate revision 1

Parent: GVG-GUARD-COMPLETE-1, under GUARD-INTERACTION-THEORY-20261025/r1.
Status: constructive Lean candidate, NOT_CHECKED and NOT_REVIEWED by this author.
Author: /root/finite_guard_completeness_astra_r1; requested gpt-6-astra/medium;
observed model/effort UNKNOWN. No coauthors or descendants at author freeze.
No production authority or native correspondence is claimed.

## Original claim and actual construction

For every n and every existing GuardedValueGraph.FiniteGraph n, the sole traversed
edge is the existing Node.next. No additional property of the graph or node
bodies is assumed by walk or decideGuard. The constructor domain is exactly the
accepted unit/pair/lam/delay/alias/view/roll/evidence research domain. In particular,
roll/view/evidence remain identity-typed in this model; this does not prove the
paper's type-changing forms.

walkAux structurally recurses on fuel. It carries a duplicate-free list seen,
seen.length + fuel = n, and a nonempty transparent path from each saved vertex
to the current vertex. Membership immediately supplies an actual cycle. For a
new vertex, Node.next = none returns that vertex, a terminality proof, exact
distance and Observes proof. A successor consumes one fuel unit and extends all
saved paths by the actual edge. At zero fuel a new vertex would give a
nodup list of n+1 members of Fin n, contradicting the constructive finite-list
bound. Thus this branch is impossible for the supplied invariants; it is not an
assumed traversal-termination fact. The cycle branch also carries Reaches from
the requested root, so a tail entering a cycle is covered.

The terminal distance is strictly less than n. height g n r computes a natural
number solely by n iterations of actual Node.next. ends_height identifies it
with the exact terminal distance once enough fuel is available. The endpoint
and distance supplied by walk derive AllEnd from NoCycle, then guardOfAllEnd
constructs rank = height g n, ceiling = n, the strict bound and strict descent
on every actual transparent edge. Its AllEnd premise is discharged by
allEnd_of_noCycle; no rank existence, chosen minimum, choice, well-foundedness
oracle or assumed termination enters the main result.

guarded_iff_noCycle combines guardOfNoCycle with the accepted
no_transparent_cycle converse. scan runs walk on the explicit List.finRange n;
decideGuard returns a computed Guarded certificate or a concrete vertex and
nonempty TransparentPath cycle. noCycleDecidable packages the same executable
case split. The empty graph needs no arbitrary starting vertex. Each root walk
uses at most n successor inspections and n+1 membership checks; scan repeats
this finite computation over n roots. This is a simple research decision,
without a native efficiency claim or benchmark.

## Application to original graph and rec extension

finite_reference_canonical and finite_no_bottom apply the constructed certificate
to the accepted canonical-observation and bottom-exclusion lemmas immediately.
Their only graph hypotheses are the original WellTyped assignment and NoCycle.

freshGraph keeps exactly those fresh Node.next edges whose target is Sum.inr;
none and old targets are terminal only for this local analysis. freshGraph_edge
proves the exact equivalence to the original fresh node's successor equation.
fresh_path_allocation transports the resulting nonempty paths to actual
allocate nodes. This makes the local criterion auditable against its constructor,
not an independently assumed transition system.

allocateFiniteGuard derives local rank, ceiling, bound and decrease from
FreshNoCycle and feeds them to the accepted allocate_guard. It allows all
fresh-to-old edges and retains the original old certificate. allocate_guard_iff
also proves necessity of the local cycle criterion under that old certificate.
finite_rec_extension supplies the original conjunction: post-allocation graph
typing, typed canonical observation of every old/new reference, and the typed
simultaneously closed body. The original old typing, per-fresh-node typing and
body typing premises remain intact. finite_rec_extension_from_cycles removes
the old supplied certificate too when the old graph is finite.

This is an application to the parent mathematical obstruction, not another
assumed-rank theorem. Subject to successful elaboration and fresh independent
review, it supplies the exact missing finite-rank completeness direction.
Luna alone adjudicates that local gate. Full-paper and native parent gates remain
OPEN regardless of the local result.

## Falsifiers and boundaries

The Lean candidate includes the following concrete constructions and quantified
proofs, not executed tests:

- zeroGraph and zeroGraph_guard handle n=0; decideGuard itself scans an empty list.
- countdown n has n+1 vertices and a maximal n-edge transparent chain.
  countdown_ends and countdown_exact_height establish its exact distance for
  every vertex; no off-by-one escape is assumed.
- selfCycle_rejected excludes a transparent self-alias.
- cycleWithTail has 0→1→2→2; tail_reaches_cycle, tail_cycle_explicit and
  tail_cycle_rejected expose both the tail and the nonempty cycle.
- sharedTerminal has two aliases reaching the same terminal; its certificate is
  obtained from constructed endpoint proofs.
- finiteMutualLambda contains two actual lambda bodies calling the opposite
  reference; its node typing and NoCycle are constructed. This permits recursive
  computation and makes no claim that evaluation terminates.
- dataSelfCycle passes the outer guard test because pair fields are genuine
  guards. No impossible finite recursive Ty equation or node-typing derivation
  is claimed for that self-pair.
- oldAliasFresh and oldAliasAllocation_guard allow a new alias to any old node,
  including an old reference domain that is not finite.

The universal proofs cover every mixed alias/view/roll/evidence chain and cycle,
all concrete data/code nodes, sharing, graph size zero and arbitrary finite size.
No whole-graph DAG condition is introduced. The list bound is reproved with
explicit DecidableEq because the general library Nodup.length_le_of_subset
proof uses classical equality. Library source for the used Fin/list/erase
lemmas was inspected; the primary must still inspect the full emitted axiom
closure. No sorry, new axiom, Classical.choice or native_decide is used in the
candidate source.

## Reuse and remaining owners

Reused only within accepted premises: GuardedValueGraph.no_transparent_cycle,
reference_canonical, no_bottom_reference, allocate_guard, allocate_typed and
closeBody_typed. The old rank-based rec_extension remains immutable; the new
finite theorem supplies its missing rank inputs instead of changing semantics.
The paper's graph-extension/value-form passages motivate the parent but do not
supply machine-checked full-paper RHS or type-changing-form premises. No prior
failed construction is revived, and no historical result is generalized by
analogy. No actual compiler/native source audit is claimed.

FGD-CHECK-1 — Luna owns primary elaboration, dependency/axiom inspection, repairs
only after acknowledged author STOP and fresh nonauthor review. Falsifier: any
elaboration failure, forbidden axiom, or finite graph for which the produced
terminal/cycle witness or strict rank equation is invalid. The exact source
suppliers are walkAux/height/freshGraph; consumers are guardOfNoCycle,
allocateFiniteGuard and finite_rec_extension. No production edit is needed.

GVG-FORMS-1 — full-paper graph proof owner: actual mu, type-changing roll/views,
type evidence and missing eliminators. Falsifier: transparent traversal preserves
this model's type but fails the real eliminator's required evidence.
GVG-REC-RHS-1 — full-paper syntax/binder owner: derive fresh NodeTyped premises
from full original rec RHS derivations under all actual binders. Existing Term
substitution covers its own five-constructor domain only.
ENV-GRAPH-1 — Luna/source intake: native graph realization from current cells,
initialization/preallocation and machine.rs Instruction::Lambda,
Frame::ValueEntry, Machine::lookup/extend and Callee, plus receiving.rs lambda
schema construction. Current graph mathematics does not establish those source
constructors emit this representation or satisfy its typing/cycle conditions.
Original F1/FK1, foreign continuations, Simple-sub generation/accumulation/
propagation/levels/extrusion/qualifying intrusion/generalization remain untouched.

## Frozen provenance and resources

Baseline: e9c0a89d2f92ac0116a75e5c7e24623e4c38acd9.
Contract SHA-256: 1d872d3972784a4f96be0d86002efa1c3e5ca369dbff6325cde86ce6537dac06.
Original author Lean SHA-256: 3a6c278bade1924344c9bae999f17145a22b09c14f31a048b97e4268f4efab77.
Final primary-repaired Lean SHA-256: a9924ab2c8d96a173c886ddfbb2580a7719fbf08064d9f85d0644784778de9fa.
Accepted GuardedValueGraph dependency:
4d2c3b17d0ab8d12606c875638426167ce596492167cecf042eb222436229f55.
Its independent CLEAN review:
d4acf31ed9546c119d697ecc5cc02c7d56d1a651fcee149980e8c987214ae3a9.
Transitive HigherOrderSyntax:
ea727d33692bdcbe6b40245b960d01225b556b5334ffab649eea2699930d5972.
Paper proposal: a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b.
Those bytes were hashed by this author and match the frozen supplied pins.
Existing Lean 4.35.0 Init libraries only; no new dependency/configuration.

Author grant: 900 wall seconds from actual dispatch acknowledgement. Exact
acknowledgement timestamp is not exposed; contract authorization
2026-10-25T06:48:53.683877+00:00 is a conservative pre-dispatch lower bound.
Primary reports actual spawn acknowledgements precede
2026-10-25T06:49:54.224226Z. First author clock observation was 06:49:09 UTC.
Freeze timestamp: 2026-10-25T06:53:38.584352+00:00. Conservative elapsed is under 300 seconds,
so more than 600 seconds of the grant remains unused; it is not a renewal.
Checks: NOT_RUN (no Lean/tests/build/checker/Git). Read-only inspections and
SHA-256 hashing only. Primary solely owns checking and review appointment.
All new paths are the leased Lean file, this note and the one assigned inbox.
No scratch files, packages, production edits, central-state writes, external
contact, background processes, nested CLI or descendants. Writer STOP after
frozen inbox creation; no further author writes or checks are scheduled.

## Primary repair and verification intake

After actual author STOP at 06:53:38.584352 UTC and acknowledged lease takeover,
/root became a coauthor. Original author inbox and its byte hashes stay frozen.
Primary repaired path_trans by applying its induction hypothesis to the second
path. The first successful elaboration still inherited Classical.choice through
library erase lemmas; the emitted full axiom closure exposed this. Primary added
explicit eraseOne/membership/length proofs and repaired nodup_length_le. A further
closure check exposed a dependency in walkAux's default order-backed membership
decision. The final source supplies memberDecidable explicitly from DecidableEq
and uses a fuel-only recursion split. Both computational decision algorithms
remain total; no rank or termination oracle was added. The unused erase import
was removed. Exact failed and intermediate passing-but-unacceptable receipts
remain in 20261025-guard-interaction-theory-r1-verification.jsonl.

Primary final candidate has elaborated. The combined query inspects all 143
public declarations across both new modules and five named query constructions,
plus 23 distinguishing examples. Concrete decideGuard projections evaluate the
empty graph, maximal chain, self-cycle, tail-cycle, data cycle, shared terminal,
mutual lambda graph and fresh-to-old alias. finiteRecApplied applies the theorem
to actual allocation/body typing. Row 16 axiom closures contain only propext and
Quot.sound. A final rebuild will bind these note bytes to the final receipt.
Fresh independent nonauthor review and primary adjudication are still pending
at this note freeze; their later verdict belongs in the sprint outcome.

Independent reviewer caught four deprecated if_true/if_false aliases in the
primary eraseOne proofs. Primary replaced exactly those aliases with
ite_true/ite_false, preserving the proof statements and construction. Renewed
final receipts include this mechanical cleanup; substantive review is unchanged.

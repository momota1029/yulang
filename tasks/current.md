# Current task: prove and implement SCC-intrusion Function inference

Updated: 2026-10-01. Branch: `research/simple-sub-intrusion`.

The user's current priority is soundness, then principality, then Oracle
compatibility. A concrete graph-level q-erasure conflict, proposed Oracle
behavior to drop, successor rule, and compatibility impact are now recorded;
the user has now directed that meaningful source constraints be retained and
approved that inference-stage scheme formatting / acceptance phase need not
match Oracle. Final acceptance of well-typed programs remains the compatibility
target. Polarity-only q erasure is not a successor requirement; retain
meaningful source constraints, and allow any later erasure only with a
preservation proof. The narrow injective pure-graph parent-transport theorem
has M3 review, conditional on the reviewed pure source/group adequacy result;
full parent semantics and Oracle projection remain open. See
`notes/progress/2026-09-30-intrusion-oracle-priority.md`. The q-erasure
inference view is followed by a frozen-Oracle mono specialization rejection
for `f 1`, so the view alone does not establish an unsound accepted program.

## Objective

Prove that the SCC-intrusion redesign can match the frozen Yulang2 Oracle's
capabilities on an explicit supported input envelope, then implement the
replacement inference machine on this branch. F5 Function generalization and
closed schemes are to be removed from the target architecture. The user's
current objective authorizes completing the proof/design and implementation
work; unresolved semantic choices still need a reviewed successor contract
before code depends on them. Frozen Yulang2 `main` at `a58eefc3` remains the
observable reference. Do not modify frozen `main`.

## Inputs and existing contracts

- `notes/design/2026-09-29-scc-intrusion-generalization-sketch.md`
- `notes/design/2026-09-29-intrude-effect-hygiene.md`
- Existing F5 contract to supersede through an approved successor: `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`, especially §§8–9, 23, 25, and 33. It is not this redesign's acceptance criterion.
- The prior `yulang3` branch retains the in-progress F5c task state at parent commit `32f0a063`; its guarded-cycle measurement budgets are consumed as recorded in the linked plans/checkpoints there.

## Active gate

Replacement-design charter: `notes/design/2026-09-29-scc-intrusion-redesign-charter.md`.
The Oracle ledger is in
`notes/progress/2026-09-29-intrusion-oracle-ledger.md`. It now includes a
reproduced source-level identity used at both `int` and Function types, plus an
unproductive mutual-recursion result and the scheduler's forward-cycle
fixture. A nominal-guarded mutual Function SCC also yields one recursive bound
per member in a temporary Oracle probe. A local diamond probe also confirms
that an enclosing non-generic variable remains shared across two result paths
and is not quantified by the inner function. A source probe for a nested local
SCC sharing such an enclosing variable failed because sequential local `my`
declarations do not resolve the forward member reference; this exact graph
case remains open and needs an accepted source construction or graph-level
characterization. A pure Function guarded mutual cycle was also observed to
collapse to `any -> any -> never` for both members, without recursive bounds;
other cycle shapes remain open. The first Gate B candidate is in
`notes/design/2026-09-29-intrusion-abstract-semantics-draft.md`: parent ports,
outer identity preservation, and independent use overlays. It includes Oracle
closure rules for a pure graph fragment and an injective-renaming lemma after
edge selection. A source audit found that lower-edge selection depends on
projection evidence, and that each member root is generalized sequentially;
root prepasses may advance the constraint epoch, while bounded post-loop passes
can mutate the solver without restarting the saved root result. The draft now
models a candidate versioned shared graph and states a root-indexed simulation
theorem rather than assuming one frozen snapshot or one equal internal graph.
This candidate remains unapproved. F5's Q/R shape, closed schemes, numbering,
and resource contract remain historical comparison points, not acceptance
criteria. The earlier auxiliary Python model has been removed from active
artifacts; its outputs are withdrawn as evidence.

The reviewed pure-F5 protocol exposed a mistaken compatibility premise and is
retained only as historical review evidence. The new lifecycle obligations
derived from Oracle SCC scheduling are recorded in the ledger. The overall
goal is proof followed by implementation, not research-only completion.

## Stop conditions and next action

Before implementation, prove the candidate semantics for its declared graph
class and supported input envelope, then record the reviewed successor
contract. Stop or revise if it
captures an enclosing non-generic variable, merges distinct polarized
constraints, shares substitutions across independent uses, loses a recursive
bound, or changes Oracle-observable behavior inside the supported envelope.
Effect hygiene and runtime freshness remain a later separate gate.

Finite examples characterize the candidate but do not alone prove soundness or
principality. Do not run guarded-cycle resource captures: the current F5c plans
on `yulang3` have consumed their authorized runs. A candidate observation
interface now compares complete source-induced contexts through machine-
specific lowerings, with internal error/fallback traces separated from public
results; independent semantic and charter reviews closed the initial relation
scope findings. Review rejected the first fixture-complete source envelope:
latent Function effect identities, tuple/record subtype rules, and guarded
recursive interval semantics are missing from the effect-free graph fragment.
The draft now separates graph-level candidate claims from source
characterization fixtures and records the current Yulang3 application/lambda
lowering gap. The effect-free Function fragment is now only a possible
component lemma; it does not redefine the objective or establish the required
Oracle-capable envelope. A canonical source grammar, machine-specific
lowering relation, generated root/use/publication traces, and candidate public
observation fields are now drafted and independently delta-reviewed. The
conditional joint-use renaming theorem now covers one identity map across all
value/effect occurrence roles, complete same-member view namespaces, and
arbitrary finite joint continuations that can relate roots across uses;
independent compiler-referee and spec-auditor delta reviews closed the
theorem's findings. The correction follows Oracle's use of one TypeVar map for
value, recursive, and Function-effect occurrences. This remains an
identity-transport lemma, not a carrier or Oracle-projection proof. The
Oracle source map found no explicit equi-recursive/coinductive subtype rule:
the Oracle uses finite polarized types, variable-bound propagation, and
recursive interval records. The unselected equi-recursive carrier cannot serve
as the Oracle basis without a separate conservativity proof. The pure-fragment
finite saturation presentation is now drafted and independently reviewed: it
uses a finite monotone closure over subtype obligations and variable
lower/upper bounds, records irreducible mismatches, keeps recursive references
as inequality endpoints, and has a conditional renaming-commutation proof. It
is not a denotation or Oracle adequacy result. The pure-fragment mismatch set
cannot be reused globally: Oracle defers tuple arity and missing required
record checks to specialization, and nominal path differences route through
`NominalCastNeeded`. Candidate `Lower -> Infer -> Spec -> Observe` signatures
are now independently reviewed, with tagged terminal outcomes, handled
fallback, a source-site map threaded through phases, and a deferred proof
ledger that is not mistaken for Oracle-emitted records. Root finalization and
the publication barrier sit inside inference; its trace preserves the Oracle-
related order without imposing a new write schedule. A read-only Oracle map
now identifies initial outcome families: entrypoint-dependent lowering
stops/diagnostics, cross-kind infer shape errors, weighted effect-filter
violations and residuals, deferred specialization failures, and the staged
nominal-cast route. Their exact public normalization remains open. Next state
the one-root transition simulation over the existing `R_i` relation, with
these tagged outcomes and source-map transport. The semantic delta review
found and closed a major gap: accumulated lowering diagnostics can stop
runtime readiness after inference but before specialization. The staged
interface now uses entrypoint-aware `Dispatch_X` with initial diagnostics to
model that route separately from inference stop. Oracle source/root adequacy
remains open. A read-only architecture investigation narrowed Gate C's
recursive denotation choice: Oracle recursive bounds are reinstalled as
inequalities, with no Oracle evidence for a recursive type constructor or
coinductive subtype rule. A carrier is still needed to prove soundness and
principality; candidate foundations and the approval boundary are recorded in
`notes/progress/2026-09-30-intrusion-recursive-denotation-options.md`. The
selected-view proof now includes a conditional renaming lemma for recursive
interval restoration, including the separate TypeVar and stack-subtraction
maps. A compiler-referee delta review closed its stack-weight coverage gap.
This remains before canonicalization and proves neither Oracle projection nor
principality; details are in
`notes/progress/2026-09-30-intrusion-recursive-interval-transport-review.md`.
The next projection-congruence source map found a further invariant: Oracle
formula selection uses numeric proof-ID canonical order and returns the first
included arm as decisive evidence, so graph renaming alone is insufficient.
The `R_i` relation now requires order-preserving proof transport or a proof
that changed witnesses cannot affect later observations. Details are in
`notes/progress/2026-09-30-intrusion-projection-order-map.md`. A conditional
query-isomorphism lemma now explains why that condition suffices for one
frozen projection snapshot: ordered visits, validation, evaluation, memo/cycle
state, and resource outcomes must correspond. Compiler-referee review found no
blocking/major issue, but constructing this relation for actual Oracle and
intrusion states remains open. Details are in
`notes/progress/2026-09-30-intrusion-projection-congruence-lemma-review.md`.
The attempt/event simulation lemma now states the required restart, wrapper,
post-loop view-construction, and full-state extension premises. Independent
compiler-referee and spec-auditor review found and closed one phase error and
the associated relation/continuation gaps; this remains a conditional proof
plan, not Gate C evidence. Exact review limits and Oracle source facts are in
`notes/progress/2026-09-30-intrusion-attempt-event-simulation-review.md`.
Next define enough of the intrusion transition semantics to instantiate its
local commuting rules, while keeping the denotational carrier and principality
choice explicit. Oracle-side facts about fresh rounds, canonical proof order,
post-loop companion mutations, and mixed-origin final views remain in
`notes/progress/2026-09-30-intrusion-projection-order-map.md`; no
cross-machine transition has been proved.
Downstream tracing now confirms that swapping two exact included proof arms
can leave compact subtype constraints unchanged but alter the stored witness
lineage and exported provenance/source site. The one-root relation therefore
must preserve normalized public provenance as well as type/query outcomes; the
narrow ordinary-use path does not use those incoming witness edges to build
subtype constraints. `BuildPolyOutput` publicly returns its subtype-provenance
sidecar, so `Observe_X` now includes entrypoint-exposed sidecars; their
identity/order normalizer remains open. This evidence is recorded in
`notes/progress/2026-09-30-intrusion-projection-order-map.md`. Settle the
semantic carrier before claiming a principal-solution theorem. See
`notes/progress/2026-09-30-intrusion-finite-saturation-review.md`. The
interface review is recorded in
`notes/progress/2026-09-30-intrusion-staged-run-interface-review.md`. The
outcome map is in
`notes/progress/2026-09-30-intrusion-oracle-outcome-map.md`. The
Oracle's Function/tuple/record/nominal/effect rules and the Yulang3 replacement
boundary are mapped in
`notes/progress/2026-09-30-intrusion-structural-rule-and-implementation-map.md`.
Tuple arity and missing required record fields can fail during specialization
after inference propagation, while nominal path mismatches route through
`NominalCastNeeded`; the inference-only closure is not the full public result
relation. The
candidate and its reviews are recorded in
`notes/progress/2026-09-30-intrusion-end-to-end-capability-matrix.md` and
`notes/progress/2026-09-30-intrusion-source-envelope-review.md`. The
conditional transport review is in
`notes/progress/2026-09-30-intrusion-joint-use-renaming-review.md`; the Oracle
subtype map is in
`notes/progress/2026-09-30-intrusion-oracle-subtype-map.md`. It remains
unselected and unproved; source-lowering implementation and the final
supported-input limits still need the reviewed successor contract. The
existing injective
graph-transport lemma remains conditional, and recursive subtype observations
are still only focused Oracle characterizations. Details are in
`notes/progress/2026-09-30-intrusion-source-envelope-review.md` and the
end-to-end source/solver gap inventory in
`notes/progress/2026-09-30-intrusion-end-to-end-capability-matrix.md`. The
unselected graph-boundary operation keeps the SCC graph authoritative and
maps source-local identities through member-owned ports to fresh per-use IDs,
while resolving preserved identities through injective shared anchors. A
focused
compiler-referee review caught and closed specific freshness, evidence-map,
imported-anchor, and memoization-scope gaps; source partition coverage and
cross-member composition remain unproved. Details are in
`notes/progress/2026-09-30-intrusion-graph-boundary-operation-review.md`. The
candidate environment convention now assigns preserved
`Free_d`/outer identities through one shared map, assigns `Gen_d ∪ Cycle_d`
through a fresh per-use map, and keeps empty fibers empty. A compiler-referee
delta review found that partition coherent after the draft required every
surviving saved-view identity to belong to one of those maps or be erased. A
follow-up review caught and closed an unbound use index in the root observation
and a source-ID/fresh-ID mismatch in the multi-use explanation; fresh-ID
independence is now conditional on the renaming lemma. This remains a
conditional candidate, not the Oracle denotation. A source
reading now records
the frozen Oracle's operational ordinary use-instantiation path: binder and
graph-node freshening, preservation of unmapped free variables, recursive-
bound restoration, stack/effect/role handling, and direct-lower vs subtype
insertion at a use site. This is not a denotational or principality proof.
Details and exclusions are in
`notes/progress/2026-09-30-intrusion-oracle-instantiation-operation.md`. A
full review and remaining obligations are in
`notes/progress/2026-09-30-intrusion-carrier-candidate-review.md`. A
focused temporary Rust Oracle probe now accepts one interval
`Bottom ≤ q ≤ Arr(Int,q)`, retaining the recursive Function upper while
discarding the trivial Bottom lower. A second probe retains matching guarded
Function shapes on both sides of one fresh variable's interval. Neither probe
selects a concrete solution, compares distinct recursive schemes, or tests
equi-recursive/coinductive subtyping; details and referee scope are in
`notes/progress/2026-09-30-intrusion-recursive-inequality-oracle-probe.md`.
Two additional independent Rust-path probes show that the instantiated
`Bottom ≤ q ≤ Arr(Int,q)` interval accepts `q <: Bottom` while retaining both
upper rows, and that `String <: q` in a separate fresh session emits the exact
constructor-versus-Function shape diagnostic. Independent referee review
confirmed these assertions and their limits: they exercise a hand-built scheme
at instantiation/constraint level, not source-to-SCC generalization or the
proposed intrusion semantics. A
first synthetic Oracle graph now combines a compatible outer lower,
an upper path to an outer anchor, and a local alias cycle. Its successful
scoped query selects the exact lower endpoint and exposes the upper anchor;
propagation lowers both local variables, which remain alongside the anchor in
the negative root with no local quantifiers. This is only graph-level
characterization: it does not prove lower-evidence transport generally. The
first source trace showed a negative Function argument reads upper records
`x ≤ e`, `y ≤ x`, `y ≤ e`, omitting `l ≤ x` from the local member root. A
second source variant puts the return variable in positive polarity; the
actual collector reads lower records for `x`, outer `l`, and `int`, and its
compact result retains `l` and `int`. The earlier interpretation as two alias
directions was incorrect: `y`'s upper `x` is the same `y ≤ x` edge. The draft
now includes an independently reviewed finite lower-graph lemma: joins of
reachable lower endpoints give a pointwise least solution and the positive
variable root denotation. It does not settle the source fixture's mixed-
polarity Function root, where argument and result identities are coupled.
The draft now states a candidate joint edge relation with shared `x` and
anchored `l`, and eliminates auxiliary `a,b` to the conditional graph image
`{ Arr(x,r) | x ≤ e, x ≤ r, l ≤ r, int ≤ r }`; selected lower records remain
replay-qualified. A focused temporary Rust-path capture now shows the saved
compact value argument/result have these conditional meet/join projections,
while the result-effect row remains outside the graph theorem; lowering adds
one forced effect quantifier. An annotated-parent source fixture now exercises
two independent uses of the same one-member recursive local scheme: the forced
effect identity freshens at each use while eleven unquantified effect
identities remain shared. A separate Rust-path source fixture confirms a
nominally guarded two-member Function SCC is quantified jointly, then uses
`helper` twice and `g` once at distinct incoming sites. Both member schemes
share a three-binder quantifier vector and retain distinct recursive roots.
The three use-value identities differ and the raw TypeVar sets in their
immediate lower predicates are pairwise disjoint; argument bounds include
`Int` and identity-shaped Function lowers. A production-instantiator trace
reports three disjoint maps for the component vector, but does not key them to
individual uses or prove transitive use-graph disjointness. The
compiler-referee review found no blocking or major issue within this narrow
characterization; it makes no intrusion-equivalence claim. For unannotated
parents, local reads keep the live value when forced quantifiers are present.
Details and review limits are in
`notes/progress/2026-09-30-intrusion-bounded-negative-counterexample.md`.
An unselected guarded-regular carrier option was blocked at Gate C by a
compiler-referee review: scheme denotation/projection equality is undefined,
recursive subtype cycles and empty environment fibers need rules, and graph
inequality cycles must remain distinct from recursive type equations. The
finite fixed-endpoint graph lemmas remain sound under feasibility and meet/join
premises, but do not cover recursive Functions or Oracle root preparation.
The findings are in
`notes/progress/2026-09-30-intrusion-carrier-candidate-review.md`; the option
has not been selected.
The Rust integration map is recorded in
`notes/progress/2026-09-29-intrusion-rust-replacement-map.md`: replacing only
F5 draft generalization is insufficient because publication, incoming-use
instantiation, and retained root projection are coupled. Further work should
use the actual Rust inference path as its characterization boundary; previous
Python-model outputs are withdrawn and cannot establish any Gate B/C claim.
The abstract semantics draft now records a root-local preparation protocol
from the frozen Rust Oracle. Source review found that component roots are
generalized sequentially, may mutate/restart at a later constraint epoch, and
can apply bounded post-loop constraints after the saved root result. The draft
replaces its single-snapshot premise with a candidate versioned shared-graph
transition and a root-indexed observable simulation theorem. Compiler-referee
and spec-auditor reviews of this lifecycle delta found and closed the epoch,
root-order, state, failure, and record-sync findings; they did not certify the
principality theorem or authorize implementation. A subsequent Oracle audit
found per-member `FetchValue`/`FetchComputation` boundaries: the same
identity-Function graph shape is generalized under FetchValue and retained as
a unit-boundary identity under FetchComputation in separate sessions. If a
mixed-fetch topology sharing one TypeVar is admitted within one SCC, a
synthetic graph refutes one component-wide quantification bit; the accepted
source witness is not established and computed-fetch cycles can diagnose. The
draft now proposes member-indexed
`Gen_d`/`P_d`, separates surviving free vars from erased variables, and adds
`Cycle_d` freshness through one source-identity map `Phi_d`. Independent
compiler-referee and spec-auditor reviews found no remaining blocking or major
issue in this parent-port/recursive-freshness delta; they support the evidence
distinctions but do not prove port selection or principality.
The latest Oracle source audit confirms that the root-indexed simulation is
still only an obligation: the state relation, principal-solution preorder,
supported graph algebra, diagnostics, and earlier-view stability are
undefined. A bounded synthetic-graph probe against an isolated frozen-Oracle
checkout found no valid two-root post-loop witness; it does not show those
mutations are redundant. Independent compiler review also required the
simulation state to include each member root, `B_d`/fetch mode, birth levels,
and `E_d` lookup correspondence, and to distinguish attempt-local query errors,
terminal latches, and surface default-root continuation. The draft now records
these obligations. Exact lifecycle observations and locators are in
`notes/progress/2026-09-30-intrusion-root-transition-audit.md`; the denotation
split and unresolved semantics are recorded in
`notes/progress/2026-09-30-intrusion-denotation-boundary-audit.md`. The next theorem
layer is split: define satisfaction and principality for an already-selected
regular member graph, then prove Oracle root/epoch projection and use
preparation produces a graph in that model. The draft now proposes an exact
principality criterion: the sound-and-complete member relation is the upward
closure of root values from satisfying local assignments, fibered over fixed
environment assignments. The multi-use relation retains each use's root result
and use-site constraints, with disjoint local assignments under one shared
environment assignment. The carrier, subtype order, and finite-scheme
representability remain open. A conditional lemma proves `Top` erasure for an
unconstrained negative-only Function argument under greatest-Top and
contravariant Function assumptions. A focused frozen-Oracle Rust-path probe
now confirms the premise for the `pub k x = 1` witness: its first compacted
Function argument is `TypeVar(2)` with no stored bounds, and the saved compact
argument is empty. This does not prove the general erasure/projection rule.
The bounded negative-argument source case is now characterized: when
`k x = expect x` constrains the argument to `int`, Oracle's first compact view
contains both the argument variable and `Int`; the saved generalized compact
root contains only `Int`, and the public scheme is `int -> int`. The
conditional counterexample and reviewed pointwise
extremal-projection lemma show that a bounded variable projects to its greatest
admissible upper type, not automatically to `Top`. Review found the
source-level singleton-bound argument insufficient as a general Oracle
theorem: eligibility, weighted aliases, rows, lower obligations, and anchors
still matter. A reviewed conditional correspondence now matches Oracle and
candidate denotations for a pure acyclic structural `Arr(x, R)` root with one
direct concrete upper atom `U`, eligible elimination, unchanged later passes,
and a separately stipulated admissible set `{A | A ≤ U}`; the precise
projection, elimination, saved-root, and later-pass premises are in the draft.
This does not prove that fiber from Oracle evidence or close Gate C. A reviewed
interval lemma shows compatible lower obligations leave the upper-bound meet
as the greatest assignment, once the exact fiber is fixed. A selected-edge
corollary derives that fiber for direct fixed-endpoint inequalities. A reviewed
acyclic upper-alias chain corollary extends the graph result to `{a | a ≤ U}`
when only the chain edges involve its
vertices and all other locals have a fixed satisfying assignment. The
`expect`/`k` source-to-view
bridge is now traced conditionally through frozen Oracle lowering, application,
Function decomposition, and scheme instantiation; the Rust probe supplies the
actual `U = Int` view and saved root for that fixture. The next bridge is to
extend this beyond the one fixture and characterize selected scoped records
and root restart/post-loop preservation. The Oracle compactor preserves an
unweighted upper alias as a secondary variable; its alias-expansion pass adds
aliases only in positive positions and flips under Function arguments. Thus
negative-argument correspondence depends on solver replay: a focused isolated
Oracle Rust probe confirms `x <: y`, `y <: U` inserts direct projected upper
`x <: U` before generalization, whose saved Function argument is exactly `U`.
An additional synthetic two-path probe confirms replay creates both upper
endpoints and finalization retains their exact `Neg::Intersection`, matching
the candidate's meet result for that graph. These are only unweighted synthetic
characterizations. A third probe observes matching `Con(U)` output for one
shared-join diamond; it does not expose path-specific replay provenance.
An isolated synthetic Oracle probe now also observes exact `Con(U)` output for
the alias cycle `x ≤ y`, `y ≤ x`, `y ≤ U`; this only characterizes that
unweighted variable-alias cycle and does not cover productive recursive
Function SCCs or selected scoped-record identity.
The candidate denotation is now proved for any finite pure variable-bound
graph with fixed concrete endpoints and compatible fixed lower bounds:
reachable upper endpoints define a pointwise greatest solution, including
shared vertices and cycles. Independent compiler-referee delta review closed
the finite-bound, outer-fiber, and greatest-projection premises. Oracle
selection/replay correspondence for that general graph class remains open;
source-level reachability, weighted paths, and general root-order simulation
also remain open.
The Oracle collector, one-polarity removal, and finalization path for this
conditional case now has independent source review. A nested captured-function
source probe exceeded its 20-second bound inside Oracle `prepare_cold` and is
recorded as no result in the progress note. Then extend the proof to anchored
or shared endpoints and continue with ordered root-step simulation,
publication/finalization, and use simulation. A two-root characterization
remains optional diagnostic evidence. A conditional lemma now shows that
injective fresh-parent renaming bijects solution assignments when finite
endpoints evaluate variable/back-edge references by direct lookup, while
keeping `E_d` anchors fixed. Recursive unfolding, root projection, and
principality remain unproved.
The first
two focused `yu-solver` Rust-path baseline
probes pass for current identity-Function and productive/unproductive recursion
behavior; they inspect F5-backed views only and are not intrusion or Oracle
equivalence evidence. The exact tests and limits are recorded in
`notes/progress/2026-09-29-intrusion-rust-replacement-map.md`. A focused attempt
to run the exact Oracle identity-use source through Yulang3 failed during HIR:
expression application and backslash lambdas are unsupported. The temporary
failing test was removed. Gate C can use a test-only semantic batch for graph
and independent-use characterization, but that cannot prove source-level
parity. Gate E must include expression application in the source envelope or
record it as a compatibility delta; a broad Oracle-capability claim requires
the source path. The abstract semantics now has a reviewed conditional lemma:
injective per-use renaming preserves finite closure, and raw use edges share
only through resolved component anchors `A_C`; closure-derived cross-use edges
through those anchors are explicitly allowed. This proves neither
solution-space independence nor principality.
Details and review limits are in
`notes/progress/2026-09-30-intrusion-factorization-proof.md`. A Rust-only
synthetic incoming-use characterization now exercises two distinct incoming
IDs with different Function constraints through the current route. It directly
observes shared argument/result identity within each use and distinct exposed
live identities across the uses. It does not establish general graph-edge
isolation, intrusion semantics, or principality. Review scope and the focused
command are recorded in
`notes/progress/2026-09-30-intrusion-rust-use-characterization.md`. General
graph isolation remains another open Gate C obligation. This witness is
current-path characterization, not intrusion correctness or source-level
Oracle parity.
Implementation remains gated on the reviewed successor contract and explicit
user approval.

The conditional member-view transition now states an evidence-admissibility
precondition: selected proof payload support includes transitive TypeVar
references from the exact root/epoch snapshot; mapped evidence uses an
injective extension of `Phi_d` and per-use `Psi o Xi`, while pinned evidence
keeps exact proof identity/dependencies opaque. Independent spec delta review
closed a port-collision finding after `Xi_d` was extended over `Local_d^+` with
full namespace freshness and fixed-anchor disjointness. This does not choose
the evidence route or prove provenance preservation. Details are in
`notes/progress/2026-09-30-intrusion-evidence-transport-precondition.md`.
Next instantiate the transition's local commuting rules against an explicit
carrier and the Oracle root/epoch simulation; do not treat this precondition as
Gate C closure or implementation authority.

A conditional semantic theorem now states that pure finite saturation
preserves the assignment fiber for every carrier satisfying its endpoint
algebra and mismatch axioms. The quantification is over stages reachable from
the initialized state, so `X` can only contain generated irreducible
mismatches. Independent compiler-referee review found no semantic finding;
spec review's minor arbitrary-state concern was closed by that reachability
condition. This does not construct the concrete recursive carrier or prove
projection/principality. See
`notes/progress/2026-09-30-intrusion-carrier-parametric-saturation.md`.
The source-generated recursive Function scheme payloads are characterized
through their quantified inner bounds. A source call through those bounds emits
nominal mismatch events that all classify as `UnknownOrigin`, leaving the check
report without diagnostics; direct and acyclic controls do report diagnostics.
The full explanation contains source leaves and an `UnknownInternal` origin that
blocks OCast eligibility. The sentinel is traced to the variable-to-variable
internal SCC edge from `AnalysisSession::constrain_open_use`. Separately, a
polymorphic nominal field selector preserves distinct recursive endpoint
payloads as inferred `int` and `bool` results without diagnostics, even though
the formatted outer schemes are identical. The raw intervals are respectively
`q ∪ int ≤ q` and `q ∪ bool ≤ q`; their conditional least-value calculation is
recorded in
`notes/progress/2026-09-30-intrusion-recursive-selector-adequacy.md`. This
narrows the next proof to source root projection and selector adequacy for
these concrete intervals. It does not select a carrier or prove general
principality. The diagnostic route remains a separate `UnknownOrigin`
observation, not subtype acceptance. The conditional algebra is reviewed; its
major overclaim about these exact bounds was narrowed and delta-closed. Next
derive which instantiated constraints produce the `int` / `bool` results.
The classifier's exact query now traces each `step <: int` event through the
recursive second invariant argument to an `UnknownInternal` root on its
bound-replay ancestry. This explains the incomplete classification locally,
without claiming subtype acceptance or identifying the origin's source.
The endpoint-bound trace now connects the producer's fresh payload lower bound
through the selector's invariant `step` comparison to the public `int` / `bool`
root. An unselected powerset carrier candidate now has an explicit tagged
universe and conditional proofs of the pure Function variance, invariant
nominal comparison, lattice, and constructor-mismatch axioms; this encoding is
independently reviewed with two notation/type gaps closed. A reviewed witness
shows that its full assignment fiber need not have a pointwise least tuple,
while the isolated local-root and
fixed-anchor projections have finite scheme representations under the
candidate subsumption relation. A pure carrier calculation now covers one
guarded negative self-cycle: its root relation is upward closed and represented
by the same finite SCC graph despite having no least full assignment; the
calculation is independently reviewed. The source trace for `pub f x = x f`
found one selected recursive interval with lower `Bottom`, then no recursive
entry in the saved view; its upper endpoint contains a negative intersection.
The earlier `q ∪ K` assignment-vacuity and `Pred`-projection explanation was
wrong and is withdrawn. Oracle path tracing still localizes the rewrite:
TypeVar2 is negative-only and eligible at the simplification boundary, then its
unreachable recursive interval is pruned. The reason this erasure preserves
the full instance relation remains unproved. The complete Simple-sub paper and
`mlsub-compare` audit is recorded in
`notes/progress/2026-09-30-simple-sub-paper-mlsub-audit.md`; the audited source
uses `(variable, polarity)` extrusion keys. Its reference writes, order-sensitive
bound snapshots, conditional preallocation simulation, and cycle/diamond traces
are recorded in
`notes/progress/2026-09-30-simple-sub-extrusion-preallocation-lemma.md`.
Independent compiler-referee review closed the nested-map-continuation proof
gap; its minor Top/Bottom representation finding was fixed by using an empty
upper-bound list whose meet denotes Top. The lemma covers preallocating names
only while replaying the same first-visit transitions; it does not prove
root-order independence, polarity merging, or Oracle projection. A variable-
only adjacent-order probe shows that opposite orders can produce different
raw graphs but the same assignment fiber; this narrows the proof criterion
from graph alpha-equivalence to the scheme relation. Details are in
`notes/progress/2026-09-30-simple-sub-extrusion-root-order.md`. The sketch now
records that distinction. Independent compiler-referee review confirmed both
traces and the fiber equality within the stated variable-only scope. A
conditional adjacent-swap argument for independent extrusion calls on a
frozen graph also passed compiler-referee review under its stated assumptions.
It does not establish Yulang root-order behavior with shared constraints or
Oracle projection. Next resolve the exact
Oracle negative-intersection projection, including latent Function/effect
identities, before resuming other source environments, interacting uses, and
OCast observations. The source
audit's polarity-sharing discriminator uses internal `L(v)=[Int]`,
`U(v)=[]` (whose meet denotes Top): positive extrusion permits its parent to
be Top, while negative extrusion permits its distinct parent to be Bottom;
identifying those parents loses that independent assignment pair under
Simple-sub's extrusion relation. This rules out calling one polarity-erasing
parent map ordinary Simple-sub extrusion equivalence, while leaving a
separately proved Yulang quotient open.
Details are in
`notes/progress/2026-09-30-intrusion-powerset-carrier-candidate.md`. The run-local observations are
recorded in
`notes/progress/2026-09-30-intrusion-recursive-root-epoch-capture.md`. The
exact cases and test limits are in
`notes/progress/2026-09-29-intrusion-oracle-ledger.md`. The concrete carrier,
scheme instance relation, and replacement proof remain open; implementation
stays gated on a reviewed successor contract and explicit approval.

## Immediate gate update (2026-09-30)

The requested full Simple-sub paper PDF and `mlsub-compare` audit is complete;
the rule-by-rule provenance table is in
`notes/progress/2026-09-30-simple-sub-paper-mlsub-audit.md`. It classifies
paper/reference ingredients as Simple-sub original, Yulang behavior/lifecycle
as extension, and intrusion/effect-hygiene proposals as new conjectures.

The powerset carrier has a reviewed conditional no-go for treating the
pre-projection q-cycle as independent subtype obligations: those edges exclude
`Top` for the negative-only argument, while erasure publishes a root with that
argument. If the projected view remains feasible, the pre/post `Pred` sets
differ. This does not refute the draft's
post-projection `Root_d`/`Pred_d` definition, whose `H_d` excludes erased
identities, and it is not a public Oracle bug claim. Details and assumptions
are in `notes/progress/2026-09-30-intrusion-powerset-carrier-candidate.md`.
Next gate: define source
typing/use observations before and after projection for the single
`pub f x = x f` view, including latent Function/effect identities, fixed
anchors, and the recursive interval's relation to the source derivation. Then
prove the chain `source constraints = pre-projection compact presentation =
rewrite/prune result = candidate H_d observations = actual finalized-scheme
use observations`. The transient recursive side table's meaning must be
explicit; do not treat it as independent interval constraints without proving
that interpretation. The complete root-epoch event inventory remains open.
The source-lowering constraint/effect shape for this fixture is now symbolically
recorded; it uses a named-self skeleton (no `SccEvent::OpenUse`), has no
unannotated-parameter call erasure, and records a subtraction fact for the
latent return-effect stack. The root/q correspondence and q visit weights are
captured for this source. Generated closure bounds and a complete proof-side
graph remain to be reconstructed.
The lowering-variable roles are now mapped to run-local TypeVar identities
for `R/S/X`, the defined-lambda skeleton, application, and wrapper in
`notes/progress/2026-09-30-intrusion-source-identity-map.md`; the q-cycle
vertices resolve to `X⁻` and `S⁺`. A follow-up trace maps every named source
effect variable and confirms the parameter's Bottom effect slot. This does not
resolve the source's pre-root constraint/event construction or the
stack-subtraction correspondence through the selected root. A focused root
attempt trace shows this fixture begins at epoch 27, settles in one attempt
without mutations/restarts in either companion pass, and saves two
quantifiers/zero recursive sandwiches. A same-source trace now maps that
generalized compact root to the finalized scheme: its argument is `Top`,
`arg_eff` is `Bot`, its result/effect variables are `Bv`/`C`, and q has no
surviving recursive row. This is representation correspondence only; the
semantic `Vpre -> Pi(Vpre)` preservation, stack-subtraction interpretation,
and replay's complete source provenance remain open. A stage trace now
observes the fixture's q rewrite (`TypeVar(2) -> None`), the still-present q
row, and its later reachability pruning. This is operational stage order only;
the one-row reachability prune follows directly once q is absent from the
rewritten root/roles. Neither result proves that the pre-projection
presentation preserves source/use observations. A conditional `Pred` equality
now covers the observed negative-only root if its recursive side table is
presentation metadata only when q's assignment fiber still admits `Top` and
the result/continuation is independent of q. A two-element counterexample
shows polarity alone is insufficient when its interval excludes `Top`;
treating the row as an independent obligation triggers the reviewed powerset
no-go. This equality remains conditional and does not characterize the source
fixture by itself.
The exact source application also contributes a direct Function upper bound on
q, so ordinary source-constraint assignment semantics excludes `Top` and
cannot justify the projection. The selected q upper plus root lower now yields
a graph-level principality counterexample: the erased scheme relation contains
`Fun(Top, Bottom)`, but the selected graph has no root below it under the
proper-Function subtype assumptions. The compact recursive upper is
`q ≤ q ∩ K(q)`; meet laws reduce it to `q ≤ K(q)`, while the full captured
`K(q)` contains a nested q Function and is not identical to the direct source
upper alone. The proposed behavior to drop, retained
parent-graph rule, compatibility impact, and full-source caveats are recorded
in `notes/design/2026-09-30-intrusion-q-bound-successor-draft.md`; it remains
unreviewed and unapproved. The captured inference-stage `f 1` / `f 2`
uses report `int` / `bool` under the q-free scheme, but a frozen-Oracle
`dump-mono` run rejects `f 1` during definition-body specialization with
`int <: Function`; a temporary trace records the exact `f` instance signature
as `int -> unit`. A Function-valued use `f id` is also rejected when the
specializer checks `f : (unit -> unit) -> unit`; the recursive `f` occurrence
is passed to `id : unit -> unit`, producing `(unit -> unit) <: unit`.
`check` and `run` on the first source did not terminate
within the observation window and were interrupted, so they give no final
entrypoint result. `dump-poly` succeeds on that same source, prints
`main : never`, and marks `main` as a runtime root; `dump-mono` then rejects
its concrete instance. The replacement draft now treats Oracle polarity erasure
as an observed projection transition, not a proved solution-preserving
simplification; scheme inference and later specialization are separate
observations. Temporary traces confirm the body check rejects both a concrete
`int -> unit` use and a Function-valued use. A code-level necessary-condition
lemma now states that every reached mono instance passes body validation under
its instance signature; it does not equate that validation with the full
inference constraint graph. Next close the effectful source-to-denotation
bridge and prove the candidate-to-Oracle relation for reached instance
signatures, then characterize entrypoint behavior without
treating `dump-mono` failure as a runtime result. Details are in
`notes/progress/2026-09-30-intrusion-powerset-carrier-candidate.md` and
`notes/progress/2026-09-30-intrusion-q-finalized-use-path.md` and
`notes/progress/2026-09-30-intrusion-oracle-instance-validation-lemma.md`; the
draft contract note is in
`notes/design/2026-09-29-intrusion-abstract-semantics-draft.md`.
The `H_d` bridge includes selected evidence and post-loop root state. Its type
component must match realized roots to `Root_d` and accepted supertypes to
`Pred_d`; diagnostics, provenance, and effects need separate observation
equalities.
Read-only collector tracing now separates the selected source-bound graph from
its `CompactRoot` finite regular presentation: transient `rec_vars` record
back-edge sides during expansion, while only surviving rows are restored as
scheme inequalities. Its cache includes `ConstraintWeight`, but recursion and
row identity use `(TypeVar, polarity)`. Source transitions reset weight to
empty at a positive Function argument and propagate incoming weight at a
negative Function argument. The saved `CompactRoot` capture at run-local root
`TypeVar(0)`/epoch 27 contains one q=`TypeVar(2)` row and three serialized q
occurrences, all with empty weight; another effect variable carries
`SubtractId(0)`. A focused Rust probe on exact source `pub f x = x f` then
logged both `TypeVar(2)` collector visits as Negative/empty and showed the
selected upper record's left, right, and outer weights all empty. Visit-level
q-weight closure is therefore established only for this captured source/root
shape. The exact collector transition writes the first q visit's `with_self`
term to the recursive-side upper row and returns q on the recursive edge;
this does not yet prove regular-unfolding completeness. Review rejected an
earlier finite-prefix claim because the emitted `CompactVar`s do not identify
the synthetic self q separately from the q inside the selected Function
bound. The second trace records this run's recursive q path as upper record 7
through `NegId(12).Fun.arg` / `PosId(8)` to `TypeVar(1)`, then lower record 4
through `PosId(4).Fun.arg` to q; lower record 2 is a separate
`TypeVar(4)` branch. A third focused Rust trace now directly confirms the
record-2 endpoint: the selected lower is `Qualified` with uncovered claim 1,
`PosId(5)` is `Pos::Var(TypeVar(4))`, and bound collection emits a secondary,
empty-weight occurrence of TypeVar4. Record 4 is separately selected for the
same source and claim and leads through `PosId(4)` to the Function whose arg
is the shared q leaf. Both q visits share leaf `NegId(4)`, so the path and
bound-record provenance distinguish the visits, not their arena leaf ID. These
identities are visible in the traversal trace but are not stored on compact
occurrences. A candidate graph must retain the bound and parent-path
identities explicitly. The q-cycle slice now records a collector-generated
`SelfOccurrence(v2-)` separately from the selected bound edges, with an
explicit forgetting map to compact syntax left to prove. A fourth focused
trace now directly closes the finite typed bound-incidence cycle:
TypeVar2-negative upper record 7 has a Function argument PosId(8)=TypeVar1;
TypeVar1-positive lower record 4 has a Function argument NegId(4)=TypeVar2.
The root lower record 24 enters through that same NegId(4), and these visited
edges carry empty weights. The live bound-record trace now resolves local
provenance: record 4 is produced by replay constraint 3 from TypeVar4 records
1/3, whose source constraints have `UnknownInternal` roots; upper record 7 is
directly from constraint 6 with `ApplicationArgument` origin. A source trace
ties that origin to boundary 0 and `x f` byte range 10..14 (callee x at 10..11,
argument syntax node 12..14 starting at f and including the trailing newline),
with values TypeVar2 and TypeVar1. This is a typed bound
graph cycle with a finite, acyclic local derivation fragment; no causal
derivation from record 4 to record 7 was found. The compact representation
still omits the edge and path identities. Other weight-bearing/effect endpoints and the bounds
reachable from TypeVar4 remain untraced. Full trace and limits:
`notes/progress/2026-09-30-intrusion-q-finite-bound-cycle-trace.md`.
Simple-sub's
`TypeSimplifier` also explicitly preserves recursive variables during
polar-only removal,
whereas the Oracle removes this negative-only q and prunes its row. That
specific behavior is a Yulang extension; its contextual preservation is a new
conjecture, not supplied by Simple-sub §4.3.1. Next complete the
identity-preserving selected-bound graph and prove its graph-to-collector map,
finite-regular-presentation correspondence, and q-erasure bridge, then use
`Root_d`/`Pred_d`. General weighted-cycle reconstruction remains open. See
`notes/progress/2026-09-30-intrusion-powerset-carrier-candidate.md`.
An independent review of the second trace confirmed root lower records 22/24
are qualified by uncovered claim 14, and the q upper plus q→TypeVar1→q cycle
remain empty-weighted. The third trace fixes that earlier trace's missing
variable-bound endpoint: record 2 reaches the secondary TypeVar4 occurrence.
The traces also observe return-effect TypeVar7/8 occurrences under inherited
`SubtractId(0)` pop-one weights and several qualified lower records, but do not
resolve every effect endpoint. Projection evidence now identifies the exact
local proof records: TypeVar1 lower record 2 is a standalone original from
constraint 2; record 4 is a replay conjunction at pivot TypeVar4 from lower
record 1 and upper record 3 (`UpperBoundAdded`, result constraint 3). Likewise,
root TypeVar0 records 22/24 share claim 14: record 22 is original constraint
16, while record 24 is a replay conjunction at TypeVar14 from records 21/23,
result constraint 17. An independent review matched these evidence variants to
the proof constructors. A fourth trace records the pivot endpoint shapes too:
TypeVar4's lower/upper premises are `Fun(arg=TypeVar2-)` and `TypeVar1+`, while
TypeVar14's are the root Function and `TypeVar0+`. Those premise lower records
are later returned as Unclaimed when queried on the pivot; their provenance is
not recursively certified by these logs. The evidence therefore supports the
local selected-record derivations and endpoint identities, not a complete
proof-provenance graph. The application-origin source ranges are known, but
the trace does not record resolved HIR/DefId binder identities or explain the
causal relation from the TypeVar4 replay to the application edge. Neither
trace includes the finalized
`CompactRoot`/scheme quantifiers or interval restoration, so the selected graph
and q-erasure preservation proof remain incomplete.
The rule distinction is recorded in
`notes/progress/2026-09-30-simple-sub-paper-mlsub-audit.md`.
This is one fixture-level obligation; multi-member epochs, publication/failure,
internal uses, and independent incoming uses remain charter-wide requirements.
No compiler implementation is authorized by this result; the reviewed
successor contract and explicit approval remain prerequisites.

The finalized ordinary-use path is now characterized in
`notes/progress/2026-09-30-intrusion-q-finalized-use-path.md`. Temporary
Rust-only frozen-Oracle probes record the exact `f` scheme and incoming uses:
type and latent return-effect quantifiers map to disjoint identities, the
Function predicate uses direct-lower insertion, and no recursive q row is
reinstalled. A non-resuming caught-use probe now follows distinct `ask` and
`tick` uses: each scheme instantiation gives `f` fresh effect identities,
initial reduction consumes both matching rows with empty residual, late replay
also consumes `ask`, and the two published wrapper schemes have `ret_eff =
Bot`. Independent review confirmed these fixture-level observations, while
noting that live catch effect variables still lack empty-row upper bounds. The
earlier `ask int` / `ask bool` handler probe remains only contextual-row
evidence. A separate local-binding fixture traces one free outer identity
shared across two uses while its local binder freshens per use; it does not
cover an SCC. Seven structural provenance witnesses remain incomplete. Next
relate selected bound graphs and q projection to source-generated constraints,
then extend the observation relation to provenance, diagnostics, and SCC uses.
These probes changed no frozen Oracle files.

The user has waived inference-stage scheme-format and acceptance-phase parity;
the target is a sound and principal successor with the Oracle's final
well-typed-program capability. A candidate acceptance contract now separates
independent declarative `WellTyped` from machine acceptance and records
soundness/completeness obligations in
`notes/progress/2026-09-30-intrusion-final-acceptance-contract.md`. Its exact
typing judgment and envelope remain undefined. Next define that judgment from
source-generated constraints and prove one frozen member's root denotation /
principality with retained one-polarity bounds over a fixed outer environment.
This is still a design/proof gate; no compiler implementation is authorized
until the exact successor contract is independently reviewed and approved.

A conditional parent-transport fiber lemma is now written in
`notes/progress/2026-09-30-intrusion-parent-transport-fiber-lemma.md`: once
the complete selected graph and anchor/local partition are fixed, injective
parent renaming and per-use freshening preserve satisfying assignments, root
values, and their upward closure for any syntax-directed preorder carrier.
It does not establish source-constraint generation or that an SCC partition
is correct. The next proof defines source typing independently of Oracle's
scheme projection, then shows that the retained component graph presents the
same source assignment relation. Oracle projection remains evidence for final
acceptance comparison, not the successor's semantic authority. The revised
candidate direction is in
`notes/progress/2026-09-30-intrusion-source-constraint-semantics-gate.md`.
The first declarative subfragment now has `Var`/`Int`/`Lam`/`App` typing and
constraint-generation rules with a conditional soundness/completeness argument
in `notes/progress/2026-09-30-intrusion-pure-source-typing-rules.md`. It does
not yet cover let-polymorphism or recursive SCCs; the candidate SCC extension
is recorded below and remains conditional.

A candidate recursive-group rule now gives each member a distinct monomorphic
self placeholder and exposed root, generates every body against the shared
self environment, and retains the full finite constraint graph as the SCC
authority. External schemes are member-specific projections with separate
generalization boundaries; each use freshens only that member view's local
and recursive identities while preserving its free anchors. Its conditional
root principality argument is in
`notes/progress/2026-09-30-intrusion-scc-constraint-scheme-rules.md`; source
constraint generation, SCC ownership, and Yulang effects remain unproved. The
`pub f x = x f` pure projection yields a nonempty retained graph and
conditionally proves that `f 1` has no satisfying instance in the candidate
carrier, matching the recorded Oracle final specialization rejection for
that fixture. The latest proof adds a declarative recursive-group rule and
proves generation adequacy/root principality for the narrow pure fragment with
a fixed outer environment. There, every SCC-created identity is local to each
member scheme, outer identities are fixed anchors, and regular cycles add no
separate binders; per-use renaming preserves the root relation. This removes
mixed local/free ownership from that fragment, but does not solve it when
nested boundaries or member-specific fetch kinds are admitted. The theorem
and limits are in
`notes/progress/2026-09-30-intrusion-pure-recursive-group-adequacy.md`. A
nested-let graph-scheme rule now defines scheme meaning by
existential graph denotation, derives `Q` from fresh RHS identities minus
environment anchors, retains binding constraints even when unused, and
clones local graph identities per lookup. Its reviewed M3 adequacy argument
states the `Γ`/`Ξ` coherence invariant, proves exact root-relation equality by
structural induction, and uses environment extensionality when the declarative
rule chooses a different but denotationally equal scheme. Recursive member
schemes can be supplied as polymorphic environment entries, but no combined
recursive-group-plus-nested-let theorem is claimed. See
`notes/progress/2026-09-30-intrusion-nested-let-graph-schemes.md`. This remains
unapproved and does not cover recursive groups nested inside expressions,
effects, or Oracle final acceptance. The combined-rule candidate and its
current review status follow.
A first composition theorem is now drafted in
`notes/progress/2026-09-30-intrusion-recgroup-let-composition.md`: it treats
the recursive group graph as a base validity witness and clones it per
continuation member use. It extends recursive-body adequacy to outer
polymorphic names through the nested-let theorem, with declarative `LetRec`
defined from source member-type sets independently of the graph generator.
Compiler-referee and spec-auditor M3 review closed concrete circularity,
environment-domain, simultaneous-update, and set-binder findings within this
pure scope. No Oracle final-capability result or implementation authority
follows yet. The final-acceptance contract candidate received M3 semantic and
specification review; both confirmed the priority but required an independent
envelope, syntax-directed source rules, explicit source-graph adequacy, and
root/use equality for every fixed outer assignment (including subsumption and
empty fibers). Those repairs are recorded in
`notes/progress/2026-09-30-intrusion-final-acceptance-contract.md`; that review
does not certify the semantics or the full Oracle envelope. The combined
recursive-group/nested-let note now also derives the `f x = x f` retained-q
constraint from the declarative source rule, excludes the erased
`Fun(Top,Bottom)` root, and derives rejection of an `Int` application under
the stated pure carrier assumptions. Focused compiler-referee/spec-auditor
review found and closed the missing least-`Bottom` premise and imprecise
erasure description; no issue remains in the pure singleton corollary. This
does not certify effects, complete Oracle behavior, or implementation. The
parent-map composition candidate received M3 semantic/specification review;
the repair now transports a complete joint relation containing base SCC
validity, every independent use copy, caller constraints, and cross-use
obligations while fixing all outer/context identities. The reviewed theorem is
conditional on the pure source/group adequacy result and does not cover the
full Oracle pipeline. See
`notes/progress/2026-09-30-intrusion-parent-transport-composition.md`. Next
extend source adequacy through ordinary implicit Function effects before
handlers: Oracle allocates latent effect identities for ordinary Functions,
special-cases pure-argument Function subtyping, and inserts call-stack
`StackWeight::push(δ, Empty)` / frame-pop evidence for eligible unannotated
local calls. The frozen source characterization and exact conditions are in
`notes/progress/2026-09-30-intrusion-oracle-latent-effects.md`; independent
compiler-referee review closed its source precision findings. Specialization
uses a two-mode *runtime shape* split: shapes with pure extracted effects
evaluate arguments strictly, while non-pure effects travel in deferred
thunks. It joins the strict argument's actual effect into the result, but
gives thunk arguments a pure immediate effect. This does not establish how
inference `arg_eff` determines the runtime shape: a Function conversion wraps
non-syntactically-pure effects such as `OpenVar`, while a variable with only
the `Bot` lower and empty-row upper materializes to the empty row if that bound
view remains available. These materializer paths are source-verified. A
temporary focused probe for `pub id x = x` found one quantifier and finalized
`arg_eff = Bot`, `ret_eff = Bot`; this source's exact-pure body effect is
eliminated before runtime materialization, which therefore leaves a plain
return shape. The probe did not identify which generalization pass removes it
or cover other Functions. The inference branch separately tests syntactic
`Neg::Bot`. A subsequent static trace identifies polar simplification as the
first conditional candidate for the `id` elimination: the effect is
positive-only after compaction, and an eligible one-polarity variable can be
removed before quantifier selection. No intermediate compact snapshot was
captured, so eligibility and absence of hidden opposite-polarity obligations
remain premises; this does not justify dropping source constraints in the
successor. This major bridge obligation was found by independent
compiler-referee review and is recorded in the latent-effects note. The next
proof must define an explicit inference-to-runtime evaluation-mode judgment;
inference-stage parity is waived, so a source-derived mode is allowed only
with a proof of equivalent final behavior. A candidate mode-indexed rule is
now recorded: runtime purity is `Never` or the empty effect row, the strict
argument contribution is joined with callee and return effects, and deferred
arguments preserve their latent effect for any later force. Compiler-referee
delta review closed its return-effect, purity-predicate, and mode-principality
wording findings; the inference-to-shape relation remains unproved. A
disposable frozen-Oracle probe now compares unused `int` versus
`[_] int` parameters applied to `out::read(())`: the plain-value specialization
forces the argument's `[out]` thunk, while the thunk-parameter specialization
wraps it in a `MakeThunk` and leaves the force inside. This establishes a
shape/evaluation distinction in generated mono structure only; no program was
executed, and the probe does not establish inference-effect adequacy. Its
independent compiler-referee review confirms only the generated shape
distinction and points out that `thunk[any, int]` is the adapted runtime
parameter shape, not evidence about the inference `arg_eff` denotation. A
second probe now confirms, for these fixtures only, finalized
`Pos::Fun.arg_eff = Neg::Bot` versus `Neg::Top`, then materialization to a
plain versus thunk argument. The effect operation has scheme
`() -> [out] int`, while both wrapper schemes render `int -> int`. Independent review
closed this narrow endpoint-to-runtime link and its caveats: it does not show
that source lowering allocated `Top`, equate `Top` with `[out]`, or generalize
to other functions. The source-level unannotated local `Def::Arg` path is now
captured for `my h(x, f) = f x`, and a second source fixture
`my h(x, y, f) = (f x, f y)` confirms one frame-local `SubtractId` is reused
across two distinct call effects, with one frame pop and a subtract fact only
on the first call effect. Compiler-referee review confirms the source
lowering lifecycle but explicitly does not prove weighted cancellation or
second-call fact derivation. A nested recursive-local fixture now confirms the
direct-call path crosses an active inner skeleton and selects the introduced
outer call frame; compiler-referee review required explicit predicate evidence
to distinguish this from a sub-syntax fallback, which the follow-up trace
provides. This still does not prove weighted cancellation. Next find a source
path where a source exact-pure identity has both polarities and inspect its
complete raw finalized predicate. Three focused fixtures (`make = \x -> 1`,
an inline lambda passed to `apply`, and a named `make` passed to `apply`) all
finalized; `make` exposed `arg_eff = Bot` and `ret_eff = Bot`, with no
quantifiers, while `apply` retained its unrelated callback effect binder.
These probes do not show the exact-pure variable elsewhere in the full
predicate and do not establish its erasure point. A source audit confirms
positive collection keeps a self-variable occurrence but projects selected
lower records; later polar simplification may erase it. Do not use this as
permission for successor q-erasure: retain the source interval until a
denotation/preservation proof justifies solving it to purity. Details and
review limits are in the latent-effects note. A `catch 1` continuation probe
now puts the scrutinee's exact-pure effect identity in both return-effect
polarities of local `k`; its finalized root still has `ret_eff = Bot`, and
the selected-root correspondence is unproved. Independent review confirmed
that graph incidence does not establish selected-root survival or final
acceptance. A second focused test appended `f()` and passed the same fixture
through production `specialize`: it produced a root call and `unit -> int`
instance with empty argument/return effects. This proves Oracle inference-to-
mono acceptance for that exact source, not runtime execution or successor
adequacy; see the latent-effects note. A wasm runtime-test attempt was stopped
before execution because the build script was compiling both embedded stdlibs
and reached about 1 GiB RSS after 2m46s. A focused disposable-Oracle
instrumentation now confirms that the actual positive `f`-root projection
visited the source effect variable with an empty projectable-lower list while
two upper rows were available; the pre-simplification root kept the positive
self occurrence and the post-alias/simplification root had no return-effect
variables. A second trace shows the first polar-elimination pass maps
`TypeVar(3)` to `None`; pinned collapse made no change and co-occurrence made
no substitution. Independent review confirms this is the operational cause
for this prepared root, not evidence that the omitted upper rows are
semantically meaningful or that the complete source graph has one polarity.
The selected `judge` root is now traced through its finalized scheme:
`TypeVar(11)` is shared between `[signal; 'a]` argument-effect tail and `'a`
return effect, and has four admitted lower records, including an
`AllExcept(signal)` weighted record. This licenses a same-identity residual
scheme characterization, not naming the records `io`, proving weighted
preservation through simplification, or proving principality. Provenance
queries map the four records to `Constraint(33,35,36,37)`; three have only
`UnknownInternal` source roots. Both leaves on the weighted path come from the
same `judge` parameter annotation `x: [_] _`: one is the annotation constraint,
the other its generated wildcard-row subtract fact. They are not act operation
signatures, and the IDs are session-local. A same-family pair now has identical
formatted schemes but different pre-simplification `ret_eff` weights:
complete carries `push(δ, AllExcept(choose))`; incomplete carries
`push(δ', All)`. This shows a selected-view distinction hidden by formatting,
not final effect semantics. The same pair now passes Oracle `check` and
production `dump --mono`; final raw type schemes are alpha-equivalent, with no
stack quantifiers or weighted return effect, while mono bodies retain their
different operation-arm sets. This proves exact-program final mono acceptance,
not runtime handler behavior or weight redundancy. A follow-up named effectful
thunk is passed to both functions; mono shows its `EffectOp` expression builds
`thunk[[choose], unit]`, and each callee forces it inside the catch marker.
Runtime source confirms `EffectOp` application constructs a thunk and
`force_thunk` emits the effect request. Interpreter execution of the explicit
thunk pair now shows the complete handler exits successfully while the
incomplete handler propagates `choose::reject` as `yulang.unhandled-effect`;
both share alpha-equivalent finalized function schemes. Read-only lowering
inspection confirms complete coverage directs the scrutinee row to the result
effect; incomplete coverage introduces a fresh rest effect and an additional
scrutinee-to-result constraint. A focused same-run trace maps the selected
`AllExcept(choose)` / `All` weights to live variables with ordinary upper
bounds, then shows both occurrences disappear in the combined alias-
simplification stage via `TypeVar -> None`; final roots retain unweighted
residual variables and the same formatted scheme. Independent compiler-
referee review confirms the root mapping and bound shapes, but not constraint
necessity or semantic preservation. The source audit maps complete-handler
boundaries 0/1 to its parameter annotation and generated wildcard-row subtract
fact, and incomplete-handler boundaries 2/3 to the corresponding pair; source
spans are not stored in boundary records, so the mapping is fixture/lowering
order specific. A same-fixture endpoint trace resolves `NegId(13)` to the
`choose` effect-family head and `NegId(58)` to `TypeVar(53)`. The complete and
incomplete `WeightedResidual` derivations both retain that family head and cite
their respective generated subtract facts; the complete path's source row
relation carries `push(SubtractId(0), All)`. A same-run emission/projection trace
now shows complete's generated gamma 28 constrained to tail variable 14 under
`AllExcept(choose)`; a selected 14 occurrence is substituted by final
quantifier 11, while gamma 28 is eliminated. This is structural traceability,
not proof the weighted edge causes Q11 or that erasing gamma preserves it.
Incomplete's gamma 53 is constrained to fresh rest 52, whose selected
occurrence is eliminated. A same-run catch-lowering trace resolves Q34's
separate route: scrutinee effect 34 is constrained to result effect 43, then
generalization maps 43 -> 34; row split gamma 53 -> rest 52 is a different
path. Complete uses result effect 14 as its rest; gamma 28 -> 14 is the
weighted edge, and selected 14 -> Q11. The selected `All` occurrence on source
35 and the split's `AllExcept(choose)` weight are distinct. A finite set-row
countermodel now refutes naive deletion of a shared gamma and all its tail
obligations: it loses the requirement that each target tail contain the
source's unhandled `other` family. This is conditional on ordinary set-row
inclusion and does not show Oracle compaction is wrong. Next define the
existential projection needed to eliminate gamma while preserving every
shared-tail constraint. A restricted lemma now proves the `take(Empty)` finite
set case by replacing shared G with least witness `A minus J`, pointwise in
every tail. Review confirms the algebra but forbids extending it to other
weights or gamma neighborhoods without proof. Generalize that lemma to
directed weights, recursive replay, and extra gamma bounds, then check it
against the root-specific complete/incomplete traces. This remains a proof
obligation, not a row denotation theorem, source acceptance mismatch,
soundness, or principality result. The successor retains meaningful source
constraints; polarity-only `q` erasure is not required.
Yulang2 inference-stage scheme
formatting/acceptance parity is not required, while final well-typed program
acceptance remains the compatibility target. Any later constraint erasure
needs a preservation proof. No soundness/principality failure is established
by the `f()` fixture; do not
restore Oracle phase parity as a goal. The probe details and command are in the
latent-effects note. A separate accepted effect-handler source,
`judge(io::read())`, specializes to an instance accepting `[signal, io]` and
returning `[io]`, with a `[signal]` marker and an `[io]` residual force in
the emitted IR. This is a useful source-to-mono witness that unrelated
residual effects survive handler specialization; it does not connect the prior
`TypeVar(3)` rows or establish runtime behavior. Reuse it as an acceptance
fixture when deriving source effect constraints and transport. A
conditional zero-consumption
lemma may reduce the handler-free, no-family fragment: Oracle's weighted row
rule uses `J = K ∩ Common(L)`, so empty row heads force no row consumption;
arbitrary heads require `Common(L) = Empty` at every split. A vacuous
“all active takes are empty” premise is insufficient when there are no active
pushes. Neither premise has been proved for generated graphs, and
the candidate carrier must define `Bot ≤ e ≤ Row([], Top)` before calling it
exact-pure. The frozen effect spec and these gaps are in the latent-effects
record. The successor must also account for scoped, noncommutative
`SubtractId` push/pop transport; those identities cannot be erased as mere
effect-family labels without contextual preservation. Then prove soundness,
principality, and source-lowering
adequacy for fixed outer assignments. Do not assume a four-coordinate product
or infer an effect algebra from renaming. In parallel, complete ordered
member-root lifecycle
simulation (epochs, saved roots, bounded post-loop mutations, and atomic
publication) before asserting Oracle SCC adequacy. Then extend the parent
operation across those effects and lifecycle transitions toward complete
Oracle final-acceptance capability. Method selection, roles, and implementation
resolution are a required later gate before successor semantics are complete
or implementation-ready. Do not start that gate until ordinary effect/handler
semantics are sufficiently settled, unless the current effect proof discovers
a concrete dependency that requires resolving it earlier. This gate is
recorded in the redesign charter. No compiler implementation is authorized by
the conditional transport result alone.

## Current user decision: independent effect semantics first

Oracle weight propagation and left/right routing are characterization evidence
only. Do not treat `StackWeight`, `SubtractId`, `All`, `AllExcept(...)`, or the
frozen routing rules as semantic authority or assume they are sound. The finite
set-row residual projection recorded in the latent-effects note is conditional
on its stated set interpretation; it is not a successor semantics theorem.

Before generalizing that projection or implementing effect machinery, define a
declarative effect/handler semantics independently of the Oracle algorithm.
Give weight an independent meaning if retaining it, and prove every left/right
transformation preserves that meaning. Do not erase, split, commute, or transfer
weighted constraints without such a proof. Search explicitly for Oracle routing
counterexamples, covering repeated pushes with one shared pop, nested frames,
complete and incomplete handlers, and residual effects. If a conflict with
soundness or principality is found, record the precise Oracle behavior dropped,
the successor rule, and the compatibility impact. A conservative
continuation-summary candidate and its independent review are recorded in
`notes/progress/2026-10-01-intrusion-coarse-effect-abstraction-candidate.md`.
Next: define provider/capture eligibility independently of family rows and
prove the candidate's complete-coverage side condition and least-derivable
bound property. The contract principle is source-backed, but provider identity,
grant lifetime, closure escape, and helper transport are not. Keep absent,
concrete, empty, wildcard, and wildcard-by-skeleton annotation forms distinct
until their successor meanings are specified. The one-step proof target also
requires `Drop` evidence across every reachable request/handler activation,
including states created when an outer handler resumes a forwarded
continuation. Only then derive any weight encoding or resume root-specific
projection work. The later
method-selection/roles/impl-resolution gate remains deferred unless this
ordinary effect proof discovers a concrete dependency.

Focused frozen-Oracle nested-provider probe: `outer(rejecter)` is accepted and
runs the outer same-family reject arm (`run --interpreter --print-roots` gives
`[1]`) even though the call passes through an inner same-family catch. Mono
shows both marker sites and the force under each. This disproves nearest-active-
handler as a routing shortcut, but does not demonstrate unsoundness: the
independent provider/handler rule is still open. A compiler-referee review found
no counterexample in that probe and confirms this limit. A followup with an
explicit `[choose]` callback capture contract lets the inner handler return
`[2]` while the no-budget pair returns `[1]` from the outer handler. This closes
the basic nested provider/capture contrast but does not explain the extra helper
boundary candidate. Details are in
`notes/progress/2026-09-30-intrusion-oracle-latent-effects.md` and
`notes/progress/2026-09-30-intrusion-weight-routing-counterexample-search.md`.

## Shallow-handler trace and soundness conflict

The first independent direct-effect calculus is drafted in
`notes/progress/2026-09-30-intrusion-shallow-handler-trace-calculus.md`. It uses
free resumable request trees and a shallow Catch transformer; it does not yet
model provider ownership or weights. The one-request fixture shows Oracle
effect rows over-approximate exact finite trace support: its continuation is
`Return`, but Oracle gives `k` the whole scrutinee effect, infers `[choose]`, and
rejects an explicit `[]` function effect; both runtimes return `[1]`. This is
not a required successor divergence. Exact traces are a soundness reference;
the successor may use a coarser sound effect abstraction, and principality must
be defined relative to the chosen abstraction. Exact continuation-sensitive
inference and linear/affine usage tracking are not requirements absent separate
language justification. The two-request case keeps `[choose]` and both VMs
report the second request unhandled, as shallow resumption predicts. No
left/right-weight cause is isolated.

The helper-boundary mismatch is now characterized through `invoke` scheme
finalization and caller application. `invoke`'s callback call contributes a
`push(choose)` lower edge, then its return endpoint carries a matching
`NonSubtract` pop; the closed scheme is `Bot`. At the helper use, the pure
instantiated return effect enters the call-result slot unweighted, and the
caller body has no `choose` row to subtract. This pinpoints where effect
information disappears, but Oracle's cancellation remains characterization,
not a sound rule. Details and bound-record evidence are in
`notes/progress/2026-09-30-intrusion-weight-routing-counterexample-search.md`.

A repeated-operation callback witness establishes the soundness conflict:
`two_requests` has type `() -> [choose] int` but performs two sequential
requests. Oracle accepts generic `via_helper(f: () -> [choose] int): [] int`
which catches one request and resumes its raw continuation. The second request
is outside the shallow handler, so a sound finite-family abstraction retains
`choose` and rejects this `[]` annotation. This deliberately drops one exact
Oracle acceptance because it is unsound; the source, transition argument, and
compatibility impact are recorded in
`notes/progress/2026-09-30-intrusion-weight-routing-counterexample-search.md`.

Temporary runtime tracing confirms a separate adapter-guard failure: the
first request reaches the matching catch with no handler boundary, and
`request_guard_for_path` skips it using the first carried provider guard. The
declarative source contract says the explicit capture contract makes this
caller handler eligible. The successor must define this eligibility
independently and not inherit the Oracle runtime guard route automatically.
The Oracle's current run therefore errors on the first request; the declarative
shallow trace would handle it, resume, then expose the second request.

A returned-callback-closure probe adds a lost-effect path: Oracle accepts
`caller(): [] int`, prints the returned closure/caller effects as `Bot`, and
both runtimes leave `choose::reject` unhandled. The successor must preserve
`choose` in the returned function's latent effect. Whether the caller's pure
annotation must be rejected depends on still-open handler eligibility. The
observations do not establish the Oracle mechanism or a general capture-grant
lifetime rule; frozen runtime guard notes include result-marker propagation
through returned functions. Inferred variants show that absent, wildcard, and
concrete-empty callback contracts retain `[choose]` and let the caller catch
return `[3]`, while concrete `[choose]` loses the closure effect and leaks the
request. This static/runtime mismatch remains evidence, not a selected
grant-closing rule. Exact traces remain the soundness reference; exact
continuation-sensitive inference is not required if it needs linear/affine
typing or a substantially richer type system. Principality is relative to the
chosen expressible effect abstraction. Details and commands are in the
candidate record above.

Runtime IR comparison now shows the concrete callback argument and escaped
closure carrying `add_id` markers, while the absent/wildcard/empty controls
retain an effectful thunk and a marked caller force. A returning-callback
control also checks, lowers, and then fails unhandled with the same pure rows;
its IR carries markers through the returned function shape. These lowering
plans plus runtime outcomes do not provide an instrumented runtime state.
Source-derived symbolic execution now accounts for G0-G7: G6/G7 are consumed
by the callback adapter even though scalar `()` drops their markers, while
the request route carries the relevant earlier marker IDs through adapter
frame exits. The frozen mono-runtime implementation's plain Catch skips using
a carried guard and the root host reports the unhandled request. Independent
review found this implementation route conflicts with the frozen marker spec:
the spec's path-prefix condition excludes own-path coloring, while the code
allows it. Therefore this is code characterization only, not successor
eligibility authority; it needs source/spec adjudication before semantic use.
The exact trace, its limitations, and source locators are in the candidate
record above. The successor must retain `choose` in the returned closure's
latent effect. The concrete Oracle case (pure caller accepted, both runtimes
unhandled) cannot be copied as a validated rule; final caller acceptance stays
open for final successor semantics until its effect abstraction is proved.
However, the current coarse whole-scrutinee continuation candidate already
predicts rejection of `[]` regardless of handler eligibility: either the
scrutinee retains `choose`, or invoking the raw continuation contributes the
pre-handler `choose` bound from the operation arm, which runs outside the
shallow catch. This is a concrete candidate acceptance delta, not a selected
final rule; the exact support remains pure in the one-request trace. Automatic
grant expiry at return is unsupported by the current returned-marker
evidence.
On the callback-returns-a-closure control, the no-contract explicit-pure
caller is rejected for `choose`; with inferred effects it retains `[choose]`
and its handler returns `[3]`. The concrete-contract inferred variant has
`Bot` rows and leaves the request unhandled. This sharpens the Oracle conflict
for this shape but still leaves source/runtime simulation to prove. Frozen
source wording supports a scope hypothesis: the maker's concrete callback
grant covers matching handlers inside maker, while the later caller catch is
outside and may handle the escaped request without inheriting that grant,
provided no other boundary masks it. This is an inference, not an explicit
escaped-closure rule. The marker spec's own-path rule is compatible with this
reading but does not establish later-caller eligibility; the no-contract
outer-handler example is only adjacent evidence. Runtime code's own-path guard
conflicts with the frozen marker spec. The candidate relation and qualifications
are in the progress record above.

Remaining gate: complete the candidate dynamic receiving-scope relation for
provider/capture eligibility, including helper boundaries, returned-closure
re-entry, force, scheme instantiation, complete operation coverage, and
callback ownership. Then prove trace soundness and least-derivable bounds for
the compositional whole-scrutinee continuation summary. Independent
architect, compiler-referee, and spec-auditor reviews found family rows alone
insufficient for handler visibility and powerset rows alone insufficient to
establish principality. Capture evidence must be scoped to its boundary and
active handler; call/force, closure escape, and scheme instantiation must not
widen it. Annotation forms (absent, concrete nonempty/empty, wildcard, and
wildcard-by-skeleton) need separate successor semantics. A finite-core
principality target now formulates effect slots as a finite powerset lattice
with a monotone constraint operator and fixed proof-carrying `Drop`; its
finite-lattice least-solution step was independently confirmed conditional on
derivations matching the lower-bound constraints. The dynamic origin quotient,
handler scope, and transfer correspondence remain unproved. Worked one/two
request and non-resumption equations now show where the coarse least row keeps
an exact-trace-pure effect while retaining the second shallow request. Details
are in the candidate record above; a compiler-referee delta check confirmed
the `Drop` values and exact trace rows for these fixed witnesses. A separate
compiler-referee delta review also found that
subtraction must quantify over all reachable request/activation states,
including forwarded continuations resumed by an outer handler; recursive
request trees need a finite-trace or finite-approximation induction. A fresh
compiler-referee delta review found no direct finite-trace counterexample once
those premises were explicit, and flagged a minor proof gap about reusing one
global arm/effect bound across forwarded suffixes. The sketch now states that
uniform induction invariant; this still leaves the conditional proof and its
semantic premises open. Then prove or replace each weight transport rule
against that abstraction,
including repeated pushes with one pop, nested frames, complete/incomplete
handlers, and residual fan-out. Do not require exact trace precision or
linear/affine usage tracking. No implementation is authorized yet.

A spec-auditor delta review found that the previous two-request witness
explained `Drop = ∅` using a second request in a matched request's raw
continuation, which is not offered back to the shallow handler. The candidate
now separates handler-offered configurations from all transformed execution:
forwarded suffixes revisited after outer resumption count for `Drop`, while
matched raw-continuation suffixes are bounded through `k : May(C)`. Thus the
two-request witness has `Drop = {choose}` and still yields `{choose}` when its
arm resumes. A conditional finite may-block provenance quotient and an
explicit row/provenance coupling obligation are also recorded. Architect and
spec reviews agree the quotient is only a proof target; dynamic activation
scope, transport simulation, and supported-envelope precision remain open.
An independent compiler-referee delta review confirmed the distinction: the
two-request case drops the family at this handler and gets it back from the
arm's `k : May(C)` bound; forwarded unmatched requests still belong in
`Origins`. The review also confirmed that any joint origin/row fixed point
would need a new combined-monotonicity proof; the existing finite-lattice
argument applies only with fixed `Drop`.
The exact delta is in
`notes/progress/2026-10-01-intrusion-coarse-effect-abstraction-candidate.md`;
this focused semantic delta is reviewed and recorded. The finite provenance
analysis remains unproved. No implementation is authorized.

The candidate now contains a proposed transfer table for those transitions.
Three independent delta reviews found and closed the concrete table defects:
helper entry must append/recompute boundaries; proven outside-scope and an
in-scope explicit grant are separate ways to clear a blocker; annotations must
keep row-side constraints separate from explicit grant metadata; and arm/raw-k
execution must drop this shallow handler while forwarded resumption restores
its captured activation identity. Scheme-local static binder freshening stays
separate from dynamic call activations. The table remains explicitly unproved;
frozen wildcard/omission visibility does not select successor semantics.
Next gate: prove the bounded-stack candidate's concrete-to-abstract
simulation and row/provenance coupling. The candidate
now retains the top `K` dynamic frames, summarizes older frames as unknown,
and joins closure/thunk snapshots by allocation site. Dynamic identities may
not be inferred from source-site or reused stack-slot equality. An independent
compiler-referee found the concrete failure case: the same static handler site
may be inside an ungranted receiving activation on one path and outside on
another, so an outside proof for one must not clear the other. Only scope
evidence valid for every concrete activation represented by a fact may
authorize `Drop`. The `K` quotient, closure-snapshot simulation, and expiry-as-
outside rule remain hypotheses, not proof. Check `α(step κ) ⊑ step#(α κ)`
for every transfer and handler observation; then measure its unknown
fallback against the supported final-acceptance envelope before deriving any
weight encoding. The reviewed candidate details are in
`notes/progress/2026-10-01-intrusion-coarse-effect-abstraction-candidate.md`.

The quotient record now bounds every carrier component (`UnknownOlder`,
snapshot/grant references, and recursive stored-value summaries) for a fixed
finite source and `K`. Independent architect review confirmed carrier
finiteness under those stated parameters. Independent compiler-referee review
confirmed the observation invariant must classify every concrete activation
pair and admit `Drop` only when every possible scope class is in
`{Outside, InsideGranted}`; `{Outside, InsideDenied}` fails. Exact operation
coverage remains separate. These close the finite-carrier and quantifier
findings only. The source-level expiry rule and the concrete-to-abstract step
simulation remain open, so the quotient is not selected or authoritative.

A compiler-referee checked the bounded top-`K` stack's primitive push/pop
simulation after repairing the tag projection and `Many`-pop alternatives. The
`K=1` `[a,b,c]` pop case is included exactly; extra tag subsets only add
abstract paths. This closes only the stack data-structure lemma. Next compose
it with handler activation, snapshots, request lineage, and captured values,
then prove the observation invariant and row/provenance coupling end to end.
The one-step source simulation and supported-envelope precision remain open.

The source request-tree snapshot candidate is now written in the same
continuation form as the shallow-handler trace calculus: `k_offer` already
contains inner handler transformations, `ScopeSnap` is observation evidence
rather than an executable stack to reinstall, raw resumption leaves `H`
unwrapped, and forwarded resumption composes `H` once. Raw and forwarded return
paths are distinguished. A compiler-referee found the former `k`/`I` wording
could apply an inner handler twice and omitted return destinations; a focused
delta review closed both findings with a nested result-changing handler. The
architect review confirms this does not require exact continuation-sensitive
effect inference: traces remain the soundness reference, conservative
over-approximation is permitted, and principality stays relative to the chosen
expressible abstraction. Next gate: give the bounded machine a representation
for the inner handler segment that simulates this request-tree composition
exactly once, then prove offer-observation coverage and row/provenance coupling.
The source-level wording review does not close the bounded-machine simulation;
no compiler implementation is authorized.

A follow-on compiler-referee review exposed a distinct completeness requirement:
losing an inner `I` snapshot must lose neither its possible offers nor the
effects of its arms. In the reviewed `u → p → g` witness, outer-resuming `u`
must run `H(I(k0))` and expose `g` to `H`; a scope-only `Unknown` would miss
that request. The candidate now gives continuation slots a top control
fallback (`UnknownKont`/`TopOffers`) over all families, operations, origins,
scope classes, and possible handler slots when wrapper identity is lost. A
fresh compiler-referee delta review closes this omission at the candidate level
and confirms the rule does not require exact continuation-effect inference or
usage tracking. Next gate: prove `TopOffers` transition coverage, static-slot
summary completeness across re-entry/escape, and row-to-offer coupling; the
bounded snapshot simulation and provider eligibility remain unproved.

The first `TopKont` fallback lemma was independently reviewed by an architect
and compiler referee. They found the initial wording did not preserve top
across returned/stored closures and thunks, force/call, imported open effects,
or the dynamic-to-static observation projection. A focused compiler-referee
delta review closed those findings at candidate level: `TopKont` is now a
symbolic absorbing summary with `⊤Eff`, `UnknownValue`, all-destination offer
fanout, per-boundary scope unions, and explicit propagation through returns,
storage, calls, force, escape, arms, instantiation, and resume. The top effect
includes unknown imported/open families, and `⊤Eff \ Drop` remains top absent a
narrowing proof. The 2026-10-01 candidate now states a set-valued
concrete-to-abstract relation, `CoverObs` for emitted request observations,
and a labelled `step#` coverage goal; it ties `TopControl` to the full top
summary and emits observations even when a request is handled on the current
edge. Focused architect/compiler-referee delta reviews closed those formulation
gaps, but the finite-interface coverage premise, transfer simulation, and
annotation/least-solution integration remain unproved. Next gate: construct
the actual finite-slot abstraction and prove each top-tainted transition
preserves control/value/effect/provenance coverage, then prove the non-top
continuation transfers. A conditional finite-carrier proposition has now been
added to the candidate: for finite source/interface slots and fixed `K`, every
carrier component is a finite product or powerset; this does not prove
concretization coverage, sound transfer, or acceptance precision. A focused
compiler-referee delta review confirmed only this conditional finiteness claim.
The finite effect lattice now also includes an unsubtractable `⊤Eff` above
finite rows; a separate compiler-referee delta review confirmed fixed-`Drop`
removal monotonicity and the conditional least-solution argument. Neither
review proves source-slot coverage, sound `Drop` construction, full transfer
simulation, derivation correspondence, or acceptance precision. Keep exact
trace semantics as the soundness reference
and principality relative to the chosen expressible abstraction; exact
continuation support and use counts are not requirements absent independent
language-design justification.

The fixed-`Drop` principality proof cannot yet be combined directly with
may-origin discovery. A compiler-referee delta review confirmed that
`remove(E, Drop(Q))` is nonmonotone over the unrestricted product when `Drop`
requires positive origin evidence, and that the row/provenance-coupled subset
is not automatically closed under componentwise meet. This does not reject a
coupled construction; it makes the next effect-solver gate explicit: either
compute and freeze a source-sound `Drop` before effect solving, or prove a
monotone coupled domain with its own least-solution theorem. Details are in
`notes/progress/2026-10-01-intrusion-coarse-effect-abstraction-candidate.md`.

The staged alternative now states an endpoint-preserving, set-labelled
forward-simulation premise over a row-free provenance/control carrier, from
which finite reachability derives offered-request coverage before `Drop` is
computed. A compiler-referee delta review found and the candidate repaired
missing non-boundary active-mask evidence in the shared concretization; a
follow-up review found no remaining mismatch across the relation, top fallback,
observation coverage, and `Drop`. This is still only a conditional theorem
target: actual source transitions, captured-wrapper and multi-shot transfer,
uniform target coverage across admissible type assignments, row-to-offer
coupling, and derivation correspondence remain unproved. Method-target
characterization is a narrow dependency of this effect gate if target sets
depend on inferred types; it does not open the full later method/roles/impl
resolution gate. Exact continuation-sensitive effect inference and linear or
affine continuation usage are not requirements; exact traces remain the
soundness reference and principality is relative to the chosen expressible
effect abstraction.

That dependency is now concrete in frozen Oracle evidence: `flip` resolves
after a receiver effect-row lower bound and is reprobed after a transitive row
fact is added (`main` at `a58eefc3`,
`crates/infer/src/analysis/tests/case_01.rs:468-502,629-672`). The staged
may-origin initialization also must cover admissible calls into exported
handler entries with client-supplied callbacks, not just the module root;
unknown provider contexts need top offers before subtraction. The narrow next
step is to characterize a row-independent superset of effect-dependent call
targets and exported-entry contexts (or prove when top must be used), then feed
that coverage into the staged simulation. Do not start the full method/roles/
implementation-resolution gate here.
A focused compiler-referee delta review found no blocking or major issue in
the updated premises and confirmed they do not establish `Drop#` or authorize
implementation. It noted and the progress note corrected the wording that
described frozen Oracle callback documentation as a successor “source
contract.”

A further narrow characterization now defines `NameTargets(s)` as all
same-named local/global effect-method definitions. In frozen `main`, the effect
method resolver filters those finite tables by collected effect paths and
returns only a singleton candidate, so every target from that resolver branch
lies in this row-independent superset. An independent compiler-referee review
confirmed the argument for known scope and complete finite registries,
including local shadowing and ambiguity. Method-value fallback targets other
than this effect-method branch and open registries remain uncovered; the next
step is to bound those fallback callable targets or widen them to unknown, then
prove row-to-offer coupling. This is Oracle resolver characterization, not
successor method-selection authority.

Source inspection narrowed the residual fallback paths: a function upper may
probe its argument effect row (already covered by `NameTargets`), then its
argument value; unresolved sites can later use role-method or record-field
fallback. Those other callable bodies can also emit offers, so the effect gate
needs a sound finite callable superset or top offers for them. This records
only the may-origin dependency and does not begin the later resolver semantics.
A conditional effect-only corollary is now explicit: an unresolved/open call
may contribute `⊤Eff` and top offers at every compatible handler, and the
fixed-`Drop` law leaves `⊤Eff` unchanged. This prevents unknown call effects
from being erased, but it is not yet a selected typing rule or an end-to-end
soundness proof; call-entry, returned-value, captured-wrapper, and re-entry
simulation still need proof.

The candidate now gives the universal `TopCall#` backstop: one finite abstract
state covering all source/interface configurations, with a full-`TopObs`
self-loop and `⊤Eff` coupling, directly satisfies endpoint/observation
simulation and cannot be subtracted by fixed `Drop`. This is a conditional
worst-case safety lemma only; it may reject ordinary closed annotations and
does not prove the front end activates it correctly. The immediate next proof
step is localizing this top fallback using finite callable target sets, then
proving the resulting row-to-offer coupling without losing the external-entry
and captured-wrapper cases.

An independent universal-top simulation audit found no blocking or major issue
under the stated premises. Its minor scope gap is closed in the candidate:
concretization, entry seeds, and `⊤Eff` coupling now explicitly span module
return, escaped values, and later client callback/closure/thunk/continuation
re-entry. The lemma remains conditional and does not establish actual fallback
placement, annotation acceptance, or principality.

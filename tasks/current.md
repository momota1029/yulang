# Current task: prove and implement SCC-intrusion Function inference

Updated: 2026-09-30. Branch: `research/simple-sub-intrusion`.

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
resolve the complete root epoch, stack-subtraction correspondence through the
selected root, or the replay's full source provenance.
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

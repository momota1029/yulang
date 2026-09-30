# Conservative continuation-summary effect candidate

Date: 2026-10-01
Status: exploratory candidate; not selected or authoritative
Scope: ordinary shallow effects and handler residuals; no weight encoding yet
Implementation authority: none
Reviewed-by: architect, compiler_referee (multiple delta reviews), spec_auditor (multiple delta reviews)

## User constraint on precision and principality

The user has explicitly ruled out exact continuation-sensitive effect inference
as a successor requirement when it would require linear/affine continuation
typing, usage tracking, or a substantially richer type system without an
independent language-design justification. Exact trace semantics remains the
semantic reference for soundness. The inference language may choose a
conservative compositional abstraction, and principality must be defined
relative to the solutions expressible in that chosen abstraction. This does
not waive soundness or justify dropping effects; it permits a sound
over-approximation when exact trace support is not expressible. The shallow
one-request/resume example is evidence that Oracle rows over-approximate exact
trace support, not a requirement to make successor rows exact.

## Question

Can a sound compositional effect abstraction conservatively account for
shallow resumption without exact continuation-sensitive inference or
linear/affine continuation typing?

The candidate below is a response to that question, not a successor rule. Its
main unresolved dependency is provider/capture eligibility: a family row does
not say which handler may consume a request.

## Candidate abstract judgment

Let `Fam` be the finite set of operation families relevant to a checked module
and its imported interfaces. A computation has an abstract immediate effect
`D_eff = P(Fam) ∪ {⊤Eff}`, ordered by subset on finite rows with `⊤Eff` above
every finite row. `⊤Eff` covers unknown or unenumerated imported families.
A computation's immediate effect `E` belongs to `D_eff`. Functions, callbacks,
thunks, and continuation values also retain a latent effect row, which an
ordinary call or force joins into the immediate effect. Sequential composition
and control-flow joins use row join.

For an operation request in family `f ∈ Fam`, the immediate effect contains
`{f}`; a request whose family cannot be enumerated contributes `⊤Eff`.
In a shallow catch with scrutinee effect `E`, let `M` contain only those
families for which every operation that can contribute that family to `E` is
both covered by an arm and eligible for this handler under a separate
provider/capture relation. Define `remove(E,M)` as `E \ M` for finite `E`,
and `⊤Eff` for `E = ⊤Eff`. The candidate handler rule is:

```text
effect(catch e with H) = remove(E,M) ∨ effect(value arm) ∨ ⋁ effect(operation arms)
```

Each operation arm receives its continuation `k` with the whole pre-handler
effect `E` as `k`'s latent effect. Invoking `k` therefore contributes `E` by
ordinary application typing. Passing or returning `k` must preserve that
latent effect in the resulting function/value type. The operation arm runs
outside this shallow catch, so its own effect is not implicitly filtered by
`M`. Incomplete coverage, unknown eligibility, or any uncovered operation
keeps its family in `E \ M`.

This rule is intentionally coarse. Exact continuation-sensitive effect
inference is not a successor requirement if it needs linear/affine
continuation typing, usage tracking, or a substantially richer type system.
Exact traces remain the semantic reference for soundness; the inference
language may conservatively approximate their support. Principality is
relative to the chosen expressible compositional effect abstraction, not to
exact trace support. In the one-request-and-resume fixture,
`k` receives `[choose]` even though its concrete suffix is pure, so the
abstract result may retain `[choose]`. That annotation behavior is a precision
choice in this candidate, not a claim that the exact trace contains a request.
The finite set domain alone does not justify principality: the empty set is
expressible and is the least exact trace bound in that fixture. Any
principality theorem must be stated for the explicit compositional abstract
judgment above, whose continuation summary deliberately forgets suffix
correlation, and prove its least derivable solution property.

No linear or affine usage accounting is needed for this transfer: an arm that
does not invoke or export `k` does not incur its latent effect through ordinary
function application. Every actual invocation, force, or later invocation of
an exported closure must continue to carry that latent effect. Whether the
language's existing typing constructs preserve this property is unproved.

## Soundness sketch and conditions

Relative to the shallow trace transformer in
`2026-09-30-intrusion-shallow-handler-trace-calculus.md`, a candidate
induction has three cases:

1. An unmatched or ineligible request remains in `E \ M`; the trace forwards
   it and reapplies the catch to the forwarded continuation.
2. A covered, eligible request invokes its arm. The arm's own effects are in
   the arm-effect union. If it resumes the raw continuation, `k`'s latent `E`
   covers every family on every suffix path, including another request in
   family `M`.
3. A non-resuming arm has no suffix execution through `k`; its arm effects
   remain, while an input family may be removed only when coverage and
   eligibility are complete for every request that could produce it.

This is only a sketch for direct request trees. It does not establish the
provider/capture relation, effect soundness through higher-order subtype and
scheme instantiation, or a source/runtime correspondence theorem. In
particular, equal `[choose]` rows can have different handler visibility; rows
alone cannot justify `M`.

## Relative principality target for the finite effect core

The selected abstraction should have a least-solution theorem, rather than
claiming that finite rows are principal by themselves. A first target fixes a
source program and its annotation contracts, with finite family set `Fam`, a
finite set `Slots` of static immediate and latent effect positions, and fixed
provenance/eligibility input:

```text
D_eff = P(Fam) ∪ {⊤Eff}
L = D_eff^Slots
```

Order finite rows by subset and put `⊤Eff` above every finite row;
`⊤Eff` denotes any concrete family set, including unenumerated imported or
future families. Join is finite-set union with `⊤Eff` absorbing. For a fixed
`Drop ⊆ Fam`, define `remove(E, Drop) = E \ Drop` for finite `E` and
`remove(⊤Eff, Drop) = ⊤Eff`: no family may be subtracted from unknown support.
This removal is monotone in `E`; if an input grows to top, its output grows to
top, and on finite rows it is ordinary set-difference by a fixed set. Thus
`D_eff` and the product `L` are finite complete lattices.

Generate a lower-bound constraint operator `F : L -> L` from the compositional
rules. Operation nodes contribute their family; sequencing, calls, and thunk
forcing use join with operand and latent effects; a shallow catch uses
`remove(E, Drop) ∨ arm_bounds`, with each raw continuation assigned the whole
scrutinee `E`. `Drop` and callback contracts are fixed inputs for this
judgment, so these transfers are monotone. Define abstract solutions as the
pre-fixed points `Sol(F) = {ρ | F(ρ) ≤ ρ}`. Derivability must be defined by, or
proved equivalent to, these generated inequalities before calling the least
solution principal.

For each handler/family pair, let `Origins(H,f)` be a sound over-approximation
of request-occurrence and handler-activation/provenance configurations offered
to that handler by shallow evaluation. It must cover every activation,
environment, use-site instantiation, recursive unfolding, closure/thunk
invocation, operation result, and forwarded continuation suffix relevant to
the static handler slot. A matched operation's raw continuation is not resumed
under this handler: its suffix is instead covered by the whole-scrutinee
latent effect assigned to `k` when the arm invokes or exports it. A forwarded
unmatched request is different: if an outer context resumes it, this handler
is re-applied to the forwarded suffix, so those configurations belong in
`Origins`. A finite `Slots` set does not make these dynamic configurations
finite; constructing a sound finite quotient or symbolic summary is a separate
proof obligation. Define `Drop(H)` only from families whose every configuration
in this handler-offered over-approximation is covered and eligible at that
activation. Unknown configurations are treated as ineligible and prevent
subtraction. `Origins` and `Drop` must be valid uniformly for all admissible
assignments and configurations in the claimed soundness domain, not only
snapshots visited by Kleene iteration. If eligibility depends on inferred
effect slots, monotonicity must be proved again rather than assumed. Row /
provenance coupling must distinguish route: contributions that may be offered
to this handler require a corresponding request fact in `Origins` or an
explicit unknown fact; contributions known to occur only after a matched
request's raw continuation are instead coupled to `k`'s latent row and the
arm/value result that invokes or exports it. Joined paths or unknown
provenance that prevent this distinction must retain both possible routes or
use unknown, so the coverage check cannot pass vacuously.

#### `Drop` complicates joint monotonicity with may-origin evidence

Write `Q(H,f)` for the request facts currently known for one handler/family
pair, ordered by set inclusion, and let
`T(E,Q) = remove(E, Drop(Q))`. The positive-evidence condition makes this
composition non-monotone over the unrestricted product: for `E = {f}`, start
with `Q₀ = ∅`, so `Drop(Q₀) = ∅` and `T(E,Q₀) = {f}`. Add one fully covered,
eligible fact `q_ok`; then `Q₁ = {q_ok}`, `Drop(Q₁) = {f}`, and
`T(E,Q₁) = ∅`. Adding that evidence decreased the result. Now add a blocked
fact `q_blocked`; `Q₂ = {q_ok,q_blocked}` revokes the drop and gives
`T(E,Q₂) = {f}`. Thus `T` is neither monotone nor antitone in the unrestricted
may-fact powerset order. The first state violates row/provenance coupling when
`E = {f}`, so it is not by itself a counterexample on the coupled admissible
states. But that invariant does not automatically give a complete lattice:
`({f},{q₁})` and `({f},{q₂})` can each be admissible for two covered eligible
origins, while their componentwise meet `({f},∅)` violates the invariant.
Therefore Tarski/Kleene leastness cannot be applied to the restricted state
space without proving a suitable lattice or closure construction.

This is not a counterexample to a coupled operator whose order and transfer
rules prove monotonicity, or to a staged analysis. It shows that the current
finite-lattice leastness result applies directly only after a sound
`Drop`/callback input is fixed. A clean candidate phase order is to compute a
source-sound may-origin and may-block over-approximation first, freeze its
conservative `Drop`, then solve effect rows. If origins depend on inferred rows
or a joint worklist is used, prove monotonicity on the actual coupled domain and
construct a complete-lattice or alternative least-solution argument for its
admissible states.

A focused compiler-referee delta review confirmed the two product-order
comparisons and the componentwise-meet counterexample. It confirmed only that
the fixed-`Drop` theorem does not automatically lift to the proposed joint
product/coupled state space; it did not rule out a separately constructed
monotone coupled domain or certify the staged provenance analysis.

### Finite may-block provenance domain (conditional construction)

A possible finite quotient keeps effect rows coarse while tracking only enough
information to justify a handler drop. For one static handler slot, abstract
request facts can have the form:

```text
ReqFact = (family, exact_operation | UnknownOp,
           origin_site | UnknownOrigin, may_blockers)
may_blockers ⊆ (BoundarySite ∪ ActiveMaskSite) ∪ {UnknownMask}
```

`ActiveMaskSite` is the finite set of source/interface slots for independently
active eligibility guards, including provider guards; any runtime mask that
cannot be projected to one of these slots contributes `UnknownMask`.

The abstract request set joins by union. `Drop(H,f)` is permitted only when
there is positive evidence that `H` is active, every fact for `f` names an
operation covered by an exact arm, and every fact has no possible blocker.
`UnknownOp`, `UnknownOrigin`, `UnknownMask`, or an absent family-to-origin
fact prevents the drop. Static sites name possible origins and boundaries;
equal site labels do not prove equal dynamic activations. A concrete callback
contract may discharge a blocker only when a separate scope proof establishes
that the handler activation is inside the receiving activation introduced by
that contract. Helper calls, force, return, closure escape, scheme
instantiation, recursive re-entry, and forwarded-continuation resumption need
explicit monotone transfer rules. Any transfer that cannot establish the
activation relation adds `UnknownMask`.

This is a finite-domain candidate, not a construction theorem. Its simulation
must prove that all concrete request/handler configurations map to abstract
facts, including requests carried through closures and requests reached after
forwarding. Its route-sensitive row/provenance coupling must map each family
contribution that may be offered to this handler to an abstract request fact
or unknown fact, and separately preserve matched raw-continuation
contributions in the latent effect of `k` and any value that captures or
invokes it. The unknown fallback is sound only under those coverage premises
and can reduce final acceptance; its precision over the supported envelope
remains unmeasured. The
least-bound argument above assumes `Drop` and callback contracts are fixed
inputs. One possible phase order is to compute a sound may-block summary first
and then solve effect rows. If origin discovery depends on inferred rows, or
the two analyses run together, monotonicity of the combined operator must be
proved; the separate finite-lattice theorem does not establish it.

### Proposed provenance transfers (unproved)

The following table is a candidate transfer contract for checking against the
source request-tree semantics. It does not adopt Oracle weights or runtime
guard routing. `Lineage` is ordered and preserves callback-boundary evidence;
`Block(H,q)` is a sound over-approximation of the boundaries that may prevent
handler `H` from receiving request `q`.

| Source transition | Candidate provenance transfer | Required proof obligation |
|---|---|---|
| Direct operation request | Add an exact `(family, operation, origin-site)` fact; retain current lineage. | Every evaluated request has a fact, including operation results and recursive calls. |
| Enter a catch activation `H` | Mark this dynamic activation active while evaluating its scrutinee and forwarded suffixes. | Activation identity and delimiter lifetime are explicit, including recursive/re-entrant calls. |
| Enter a callback receiving boundary `b` | Append the fresh boundary instance to the lineage; compute possible blockers relative to the receiving handler activations. | Dynamic nesting and the provider of the callback are preserved across the call. |
| Concrete callback argument contract `[F]` | Record a candidate grant `(b,F)`; it can discharge blocker `b` only for family `f ∈ F` and a handler proved inside this receiving activation. | Contract ownership and scope are stable under helper calls and do not become a family-wide grant. |
| Concrete empty, absent, wildcard, or wildcard-by-skeleton annotation | Preserve the exact annotation form and its row-side constraint separately from explicit grant metadata; do not collapse the forms. | Frozen Oracle uses distinct row-side constraints (`take(Empty)`, `take(All)`, or omitted) and concrete heads alone generate explicit runtime contract metadata. Their successor visibility meaning is open; unknown meaning cannot prove a drop. |
| Ordinary helper call | Preserve existing request origin and lineage, append any newly crossed receiving boundary, then recompute handler-relative blockers for newly entered activations. Add `UnknownMask` if context prevents proving those relations. | Compositionality across argument passing, helper entry/return, and any handler entered by the helper. |
| Thunk force or closure invocation | Preserve latent request facts, then relate the current handler activation to every captured boundary; unknown relation adds `UnknownMask`. | Return/force and re-entry preserve effects and do not widen grant scope. |
| Closure return or storage | Carry latent row and provenance with the value; do not convert grants into transferable permission. | Later invocation reconstructs a sound receiving/activation relation, or conservatively becomes unknown. |
| Scheme instantiation | Freshen identities owned by local static binders while preserving imported/outer provider identities; transport request facts consistently. Dynamic receiving activation identities are allocated later, at calls. | Static binder ownership, use-site substitution, and later dynamic activation are separate; unresolved ownership adds `UnknownMask`. |
| Handler value arm or matching operation arm begins | Remove the current shallow handler activation from the active stack while evaluating the arm; arm-originated requests are analyzed against outer active handlers. | Arm execution does not accidentally reuse `H`'s eligibility or hide arm effects from outer handlers. |
| Matched request resumes raw `k` | Execute the suffix without automatically reinstating this matching `H`; retain its request lineage and analyze it under whatever outer handlers are active. | This agrees with the shallow trace transformer; effects remain covered by `k : May(C)`, and any separately installed/re-entered handler gets its own provenance analysis. |
| Forwarded request resumed by an outer context | Preserve request provenance and re-enter the forwarded handler transformer under its captured `H` activation identity. If an abstract implementation uses a successor identity, prove it equivalent for visibility. | Every such successor configuration is represented in `Offered`; arbitrary finite resumes remain covered. |
| Handler arm returns or aborts | `H` remains inactive after arm entry; finalize that same suspended scope without popping `H` or disturbing outer handlers a second time. Unwind arm-local activations normally. | Delimiter scope ends on every arm exit path and its captured identity cannot leak to unrelated calls. |

For a handler/family pair, a blocker can be removed only after exact operation
coverage and active-handler status are established, and either (a) a proof
shows this handler activation is outside the receiving activation represented
by that boundary, or (b) a matching concrete grant is in scope for this
handler. Possible-but-unproved scope is not treated as outside; it maps to
`UnknownMask`. Join of control-flow paths unions request facts and possible
blockers. This is designed to lose precision monotonically: adding a possible
path cannot create a new `Drop` proof.

The transfer table is not yet a finite abstract interpreter. In particular,
the rule for determining whether a handler is inside a receiving activation
cannot use source-site equality: recursive calls and escaped closures can
re-enter one site under distinct dynamic activations. Fresh dynamic identities
must also be distinguished from static boundary binders freshened during
scheme instantiation. A finite activation quotient and simulation theorem are
still needed. If the quotient or callback facts depend on inferred effect
rows, the combined origin/effect analysis must also establish monotonicity;
otherwise the fixed-`Drop` leastness theorem does not apply.

#### Staged may-origin closure theorem target

A phase-separated construction avoids making `Drop` an effect-solver transfer.
Let `S#` be a finite **provenance/control-only** configuration carrier for one
fixed source module and a finite interface summary denoting all admissible
client/provider contexts, not only execution from the module's own entry
point. It may contain callback contracts and source-level call-target
possibilities, but no inferred effect-row slot; open or unknown interface
behavior widens to unknown targets/offers. Its value
facts record runtime kind, finite source/call-target slot, and captured
control/wrapper references, but contain no latent-effect field. `UnknownValueP`
is defined as a top control/provenance summary that can reach every compatible
local target and emits top request observations; it does not carry `⊤Eff` in
this phase. The effect solver's row-to-offer coupling handles `⊤Eff`
separately. Define `γP(s)` directly over runtime configurations: (1) the
concrete stack and lineage are covered by the abstract suffixes, (2) every
reachable runtime value maps to a finite abstract value slot that covers its
kind and captured control/wrapper references (or to `UnknownValueP`), (3) each
concrete handler/request/boundary and other-mask relation is covered by the
scope and blocker evidence in the abstract request facts, and (4) the current
control point and pending executable wrappers map to abstract control facts.
There is no inferred effect-row inclusion or latent-row claim in `γP`. A
reachable abstract transition is labelled by a **set** of edge observations:

```text
→# ⊆ S# × P(Obs#) × S#
Post#(X) = X₀# ∪ { s' | ∃s ∈ X, Ω, s →# Ω s' }
Reach#    = lfp(Post#)
Offers#(Reach#) = ⋃ { Ω | ∃s ∈ Reach#, s', s →# Ω s' }
```

Silent edges have `Ω = ∅`; one abstract edge may emit multiple offers or
`TopObs`. `Post#` is monotone over the finite powerset lattice `P(S#)`, so
`Reach#` is reached after finitely many additions.

Assume initial coverage: every concrete initial configuration is in
`γP(s₀)` for some `s₀ ∈ X₀#`. This includes calls into every exported callable
entry, callback, or thunk that an admissible client can invoke, with the
provider/scope context allowed by its interface; it is not just the module's
ordinary root execution. An unenumerated client value or provider context must
start as `UnknownValueP`/top offers at every compatible handler slot. Assume
forward simulation: for every reachable
pair `κ ∈ γP(s)` and concrete labelled step `κ -O→ κ'`, there exist `s'` and
an edge label `Ω` such that `s →# Ω s'`, `κ' ∈ γP(s')`, and for each concrete
request observation `o ∈ O` there is an `ô ∈ Ω` with `CoverObs(o, ô)`. The
edge observation must retain the concrete handler activation, operation,
family, lineage, every receiving-boundary scope class, and every other active
mask that can independently block eligibility. An unresolved mask maps to
`UnknownMask`; a fact carrying it cannot authorize subtraction. In particular,
a request is emitted before matching/forwarding so a handled-and-vanished
offer is still covered. This endpoint-preserving simulation premise, by induction
over finite concrete paths, derives that every concrete reachable state is
represented in `Reach#` and every concrete handler offer is covered by
`Offers#(Reach#)`; offer coverage is a conclusion, not an extra assumption.

Derive `Drop#` only after this closure. It is sound only if the universal
eligibility test sees, for every offered family, all covered operations, the
full set of possible scope classes for each concrete
`(handler activation, request, boundary)` relation, and every other possible
eligibility mask. Any `InsideDenied`, `Unknown`, or unresolved blocker prevents
subtraction unless a corresponding in-scope grant is proved. This is the same
invariant required by the observation/refinement condition below, including
offers that vanish on their emitting edge. In addition, for every admissible
source/type assignment, row/provenance coupling must classify each family
contribution by route. A contribution that may be offered to this handler
needs a corresponding reachable `ReqFact` or explicit unknown; a contribution
known only behind a matched raw continuation needs the separate `k` latent-row
and arm/value preservation obligation. Open/imported rows, unresolved call
targets, and joined or otherwise unclassified routes force unknown/top for
offer eligibility. This uniform premise is not proved by reachability alone.
Target coverage is
uniform over every type/effect assignment admissible under the successor
semantics: phase one cannot use one post-inference target snapshot. It must
include every compatible target in a row-independent superset or widen an
unresolved selection to `UnknownValueP`/top offers.

A compiler-referee delta review initially found that the shared full-state
`γ(A)` omitted non-boundary active masks even though `CoverObs` and `Drop#`
required them. The relation now requires each such mask in `may_blockers` or
`UnknownMask`; the finite blocker domain includes `ActiveMaskSite` for
source/interface guard slots, and unprojectable masks widen to `UnknownMask`.
A follow-up delta review found no remaining mismatch among `γ(A)`, `TopObs`,
`CoverObs`, and `Drop#`. This closes only that formulation gap. The staged
may-origin theorem still assumes rather than proves the actual transition
simulation, interface/type-assignment uniformity, row-to-offer coupling, and
source derivation correspondence.

The current source proof also exposes a narrow method-selection dependency.
Frozen Oracle tests resolve effect method `flip` after a receiver effect-row
lower bound appears, and reprobe an unresolved selection after a transitive
effect fact is added (`main` at `a58eefc3`,
`crates/infer/src/analysis/tests/case_01.rs:468-502,629-672`). Thus a phase-one
target set cannot be derived from one pre-solve selection snapshot. For this
effect gate only, characterize a target superset uniform over admissible
assignments or use top for unresolved selections. This is the charter's narrow
dependency exception, not the later full methods/roles/implementation
resolution gate. Independently, a module-root-only initial state misses
admissible client calls into exported handlers with callback arguments; frozen
Oracle documentation records that an uncontracted callback's effects remain
hygienic (`main` at `a58eefc3`,
`web/docs/reference/effects.md:244-261`). Such entry
contexts must be represented or widened to top before any family can be
subtracted. These are concrete coverage obligations, not claims that Oracle's
effect routing or visibility rules are successor authority.

An architect's bounded source/runtime map confirms the transition cases the
future finite machine must cover: direct operation, application/force, catch
entry and return, request observation before handle/forward, raw continuation,
forwarded wrapper, and value/closure/thunk storage, escape, re-entry, and
repeated resume. Its source-level raw/forwarded cases agree with this trace
reference; no bounded `γP`/`step#` simulation has been constructed. The smallest
next proof slice remains a closed finite fragment with these transitions,
endpoint-plus-offer simulation, and row-to-offer coupling. Before that slice can
justify any `Drop#`, resolve the newly discovered uniform target and external
entry coverage dependency above. Full method/roles/implementation resolution
remains deferred.

A focused compiler-referee delta review found no blocking or major issue in
these new entry/target premises. It confirmed the cited frozen-Oracle tests
support only the narrow target-superset dependency, that all compatible targets
or top must be covered, and that the full method/roles/implementation gate
remains deferred. Its minor wording finding was repaired above. The review
closed only this formulation and handoff; it did not establish a sound
`Drop#`, concrete finite transition machine, or implementation authority.

#### Candidate target superset for the frozen effect-method branch

The frozen resolver exposes a simple finite **characterization** for just its
effect-method branch. At a selection site `s` with method name `n` and known
local scope `m`, define `NameTargets(s)` as the union of every definition
registered under `n` in the local-scope effect-method table and the global
effect-method table. `probe_effect_select_pos` first collects effect paths
from the receiver's effect component, then `effect_method_for_paths` filters
same-name local candidates by exact path and returns a target only for a
singleton; if that does not resolve, it tries same-name global candidates the
same way (`main` at `a58eefc3`,
`crates/infer/src/analysis/session/selection.rs:438-448,864-888`; the local and
global tables are exposed at `crates/infer/src/methods.rs:244-255,316-331`,
and singleton conversion is at `crates/infer/src/analysis/mod.rs:775-783`).
Therefore every target returned by this effect-method branch under any effect
row assignment lies in `NameTargets(s)`: path filtering can remove candidates,
but cannot introduce a definition outside the name tables. This gives a
row-independent finite superset for that branch when the source and imported
method registries are closed and finite. It deliberately keeps candidates that
no particular row assignment selects, so this only establishes target
coverage, not precision, principality, or final acceptance equivalence.

The subsequent method-value fallback may itself reach this same effect-method
helper through a function's argument-effect row, which is still covered by
`NameTargets(s)`. This characterization does not cover its other callable
targets, such as value/ref or role method lookup, or open imported method
registries.
Such a site needs a separate sound callable-target superset; until that is
established, it contributes `UnknownValueP`/top offers to all compatible
handler slots. The result describes frozen Oracle's resolver for
the narrow dependency only. It does not adopt Oracle's row collection,
weight interpretation, method selection, or later role/implementation
semantics as successor authority, and it does not settle how much this
over-approximation changes final annotation acceptance.

A focused compiler-referee review confirmed the `NameTargets(s)` superset for
the frozen effect-method helper with a known scope and complete finite
registries. It found that method-value fallback can also reach that helper, so
only the other callable fallback targets remain outside this characterization.
The review did not establish successor callable-target coverage or soundness
of the phase-one transition relation.

Primary source inspection further locates the uncovered fallback: the Oracle's
`probe_method_upper` checks a function's argument-effect component, then its
argument value; after receiver probes, unresolved sites can resolve through a
role method, then fall back to a record-field constraint (`main` at
`a58eefc3`,
`crates/infer/src/analysis/session/selection.rs:412-435,732-773,890-910`;
`crates/infer/src/analysis/session/lifecycle.rs:846-935`). Each selected body
may contribute offers. Until a source-level callable superset covers these
paths, the effect gate needs unknown/top offer coverage at every compatible
handler. This accounts for the dependency without defining successor role or
record selection semantics; those remain in the later required gate.

#### Conservative unknown-call consequence (conditional)

For an open or unresolved callable target that has no proved finite
`FallbackTargets(s)` superset, one candidate is to assign the call's immediate
and latent effect summary `⊤Eff`, and place top offer/blocker facts at every
compatible handler slot. The existing effect lattice defines
`remove(⊤Eff, Drop) = ⊤Eff`; therefore no finite handler drop can erase any
effect contributed through that call. The top observation also prevents the
call from supplying positive eligibility evidence for a finite `Drop#`.
This is a conservative fallback corollary, not a selected source typing rule:
it is sound only if every concrete target/effect is represented by `⊤Eff` and
the top offers simulate call entry, returned values, captured wrappers, and
later re-entry. Unknown target typing and annotation acceptance remain outside
this effect-only statement.

A deliberately coarse completion of that conditional fallback is available as
a proof lemma. Let `TopCall#` be one finite abstract configuration whose
concretization includes every source configuration over the checked module's
whole lifetime and every admissible client/interface context, including after
module return and escape into a client followed by callback, closure, thunk, or
continuation re-entry. Represent these contexts through the finite interface
summary and its unknown slots, not by enumerating client programs. Include all
bounded stack/lineage alternatives, all static control and value slots,
unknown callable/wrapper references, every scope and blocker possibility, and
top request observations. Seed `TopCall#` for every admissible exported or
client entry. Let
`step#(TopCall#)` include the self-loop labelled by the full finite `TopObs`
set. Then for every concrete transition `κ -O→ κ'` in this scope, both
endpoints are represented by `TopCall#`, and each `o ∈ O` has a covering
`ô ∈ TopObs`; hence this single abstract edge satisfies endpoint-preserving
observation simulation. The claim follows directly from the two top-state
definitions, and induction covers every finite concrete path. Couple any
immediate or latent effect slot reached through top, including escaped/stored
values and later re-entry, to `⊤Eff`; then the fixed-`Drop` law retains `⊤Eff`,
so this fallback cannot erase an effect. It also cannot prove
any finite drop because `TopObs` includes unknown blockers and families.

This is an intentionally degenerate safety backstop, not the desired ordinary
inference machine: reaching it can make every handler residual top and reject
otherwise well-typed closed annotations. It proves neither that the source
front end reaches this state exactly where needed nor that final acceptance is
preserved. The useful next refinement is to replace `TopCall#` with a finite
row-independent callable target set where one is proved, keeping this universal
state for open interfaces and unresolved targets. Exact continuation support
and use counts are still unnecessary for the backstop proof.

If these premises hold and `→#` is independent of inferred effect rows, freeze
`Drop#` and solve the effect lattice with `F_Drop#`. The reviewed leastness
result then applies, subject to source derivations matching its inequalities.
This phase order needs no continuation-use count: finite reachability closure
represents any number of resume/re-entry cycles. It can still lose acceptance
precision when unknown control or interface slots add extra offers; exact
continuation trace support is not required. The decisive open premise is a
sound effect-row-independent transition relation. It must preserve the
captured wrapper/value relation through return, storage, escape, re-entry, and
multi-shot calls, or widen to a proven top summary. If possible call targets
depend on inferred types or method resolution, include every compatible target
or an unknown summary; incomplete targets cannot justify `Drop#`.

### Bounded dynamic-scope quotient candidate (unselected)

Independent architecture and semantic review suggests a finite, deliberately
conservative route. A concrete state `κ` would carry unique dynamic handler
and receiving-boundary identities, their ordered active delimiter stack,
request lineage, contract grants, and the provenance snapshots carried by
closures, thunks, and continuations. For a fixed finite program and an
analysis parameter `K`, an abstract state can retain only the top `K` stack
frames, each tagged by frame kind and source site, plus an `UnknownOlder`
summary for frames below that suffix. Request lineage can use the same bounded
ordered representation and an `UnknownOlder` tail. This gives a finite domain
for fixed `K`; it is an analysis precision parameter, not yet a selected input
limit or compatibility boundary. To keep the carried-value component finite,
closure/thunk/continuation provenance would be joined by static allocation
site or a finite set of instantiated value slots; if recursive specialization
can create an unbounded slot universe, it must use allocation-site summaries
or `Unknown`. Grant families and paired-snapshot references must range over
finite source sites, annotation heads, bounded abstract frame positions/value
slots, or `Unknown`; they cannot use fresh dynamic counters. `UnknownOlder`
must be a finite flag or subset of finite site/kind labels, not an unbounded
count or list. Recursive stored-value depth and repeated grant instances join
at allocation sites/value slots, with multiplicity discarded. A merge may add
possible scopes but must never turn uncertainty into proof of visibility.

The abstract identity of a frame is its position in the currently retained
stack snapshot, never its source site or a position reused after pop. Such
positions cannot escape as durable identity: a closure/thunk/continuation may
carry a paired snapshot only while a proof ties it to the same live dynamic
frame. A join of equal site/position shapes with different dynamic identities
must destroy that correlation; a later transfer cannot reconstruct
`InsideGranted` from shape equality. At escape, truncation, merge, or re-entry
where identity is ambiguous, the carried relation degrades to `Unknown`. This
prevents a recursive activation or reused stack slot from inheriting another
activation's grant.

For each offered request, handler, and boundary represented in its lineage,
the abstract scope relation is a set of possible classes:

```text
ConcreteScopeClass = Outside | InsideGranted | InsideDenied
AbstractScopeClass = Outside | InsideGranted | InsideDenied | Unknown
```

`Unknown` is abstract-only. Its concretization is the full
`ConcreteScopeClass` set; a lost boundary identity must not be represented as
the singleton concrete class `Unknown`.

For an abstract set `S ⊆ AbstractScopeClass`, its concrete meaning is
`γscope(S) = (S ∩ ConcreteScopeClass) ∪ (ConcreteScopeClass if Unknown ∈ S)`.
`UnknownMask` similarly denotes any concrete blocker state. A request fact
covers a concrete scope observation only when that observation lies in
`γscope(S)` for every corresponding boundary occurrence. The universal `Drop`
test is evaluated over these concretizations, so any abstract `Unknown`
prevents subtraction.

`InsideGranted` requires proof that the handler is nested under the same live
receiving activation and that its concrete grant covers the request family.
`Outside` requires proof that the handler is not nested under that activation,
including a proof that the carried boundary has expired; treating expiry this
way remains a source-level hypothesis to validate. Any hidden stack
frame, mixed dynamic activation, unmatched snapshot, or uncertain grant adds
`Unknown`. The finite relation uses union at joins. A family may enter
`Drop(H)` only if every represented operation is covered and every possible
scope class for every boundary is either `Outside` or `InsideGranted`; any
`InsideDenied` or `Unknown` prevents subtraction. This universal condition is
important: a static handler site may denote one activation inside an ungranted
boundary and another outside it. The outside activation cannot clear the
inside activation's blocker.

#### Stack projection and primitive transfer lemma

The stack carrier itself can be made explicit independently of handler
eligibility. Let `Tag` be the finite set of frame descriptors `(kind, site,
grant-heads)` plus `UnknownFrame`, and fix `K ≥ 1`. A concrete delimiter
stack is a word `w = P · S`, where `S` is its newest suffix of length at most
`K`; `P` is the older prefix. Define:

```text
count(P) ∈ {Zero, One, Many}   // Many means at least two
tags(P)  ⊆ Tag
αK(w) = (tag(suffixK(w)), count(P), tags(P))
```

An abstract stack state is a finite set of these triples; control-flow join is
set union. `Many` stores no unbounded count or order. Abstract push of tag `x`
is exact when `|S| < K` (then `P = ε`), and when `|S| = K` it shifts the first
tag of `S` into `P`, appends `x`, and updates `count(P)` by saturating
`Zero→One→Many→Many` and unions the shifted tag into `tags(P)`.

Abstract pop removes the top of the abstract suffix `S`. If `|S| < K`, `P`
is empty and the suffix simply shrinks. If `|S| = K` and `count(P)=Zero`, the
suffix shrinks to `K−1`. If `count(P)=One`, any possible tag in `tags(P)` is
exposed at the front of the new suffix and the prefix becomes empty. If
`count(P)=Many`, the new suffix prepends any tag in `tags(P)` to the first
`K−1` retained tags, and the remaining prefix count may be `One` or `Many`.
For each choice of exposed tag, `step#` enumerates all nonempty remaining tag
sets `T' ⊆ tags(P)`; when the remaining count is `One`, it enumerates singleton
`T'` only. This can add impossible combinations but includes the exact tag set
after every concrete pop. These rules never infer a frame identity from its
tag.

For concrete stack push/pop, the primitive simulation condition
`αK(step(w)) ∈ step#(αK(w))` follows by cases on `|S|` and
`count(P)`. The only information discarded is older-frame order, multiplicity
beyond two, and dynamic identity; that loss can cause `Unknown`, but cannot
prove an inside/granted or outside relation. This is a stack-operation lemma
only. It does not prove that source handler eligibility is determined by this
stack, nor does it cover captured snapshots, request-lineage correlation,
source values, or row/provenance coupling. Those require a concrete source
activation semantics and separate observation simulation.

An independent compiler-referee delta review checked the concrete push/pop
membership cases. For `K=1` and concrete `[a,b,c]`, `αK([a,b,c])` is
`([c],Many,{a,b})`; pop enumerates `([b],One,{a})`, the exact projection of
`[a,b]`. Zero and One prefix cases are direct, while Many covers both a
two-frame prefix (becoming One) and longer prefixes (remaining Many). Extra
tag subsets add only abstract paths. This closes the primitive stack
projection check, not the handler-scope or source-transition simulation.

#### Shallow handler snapshot transition candidate

To distinguish handler restoration from stack push/pop, use a concrete
delimiter configuration `O · H · I`: `H` is the dynamic handler activation,
`O` the outer delimiter stack, and `I` the delimiters suspended between `H`
and the current request or return. Give continuation snapshots an explicit
kind:

```text
Raw(h, k_offer, ScopeSnap)       // matching arm's already-transformed continuation
Forwarded(h, k_offer, ScopeSnap) // outer request continuation wrapped by H
```

Here `k_offer` is the continuation already presented at `H`, after any inner
handler transformers have composed around the underlying suffix. `ScopeSnap`
is provenance for abstract observations, not a second executable stack to
reinstall. In particular, applying `k_offer` must not also push the inner
segment `I`; that would apply an inner handler twice. A machine that instead
stores an underlying continuation `k0` must define and prove the corresponding
single application of the `I` transformer. This candidate uses the
request-tree form below and leaves its bounded machine encoding open.

The source request-tree transition candidate is:

| Event at `H` | Concrete transition |
|---|---|
| Enter `catch_H C` | Allocate fresh dynamic identity `h`; evaluate `C` under `O·h`. |
| `C` returns `v` | Remove `h`; run the value arm under `O`. |
| Request `q` is eligible and covered | Capture `Raw(h,k_offer,ScopeSnap)` and run the operation arm under `O`. A call to raw `k_offer` clones the continuation and evaluates it with its already-composed inner handler behavior; it does not reapply `H`. |
| Request `q` is uncovered or ineligible | Forward `Request(q, x -> H(k_offer(x)))` to `O`, retaining the same semantic activation identity `h` in the wrapper. If an outer handler resumes it, the wrapper reapplies `H` to the suffix; if the outer context aborts, the suspended wrapper is discarded. |
| A resumed raw suffix returns `v` | Return `v` to the matching operation arm's call to `k_offer` under `O`; inner return/value behavior in `k_offer` runs once, while `H`'s value arm does not run. |
| A resumed forwarded suffix returns `v` | Its already-installed `H(k_offer(...))` wrapper runs inner return/value behavior and then `H`'s value arm once, before returning to the outer resumer. |
| Continuation is resumed more than once | Clone the corresponding immutable snapshot for each resume and join the resulting paths; no usage count is introduced. |
| Arm exits | `h` is already inactive; finalize its suspended scope once and preserve outer activations. |

#### Finite continuation-summary encoding candidate

The bounded machine should not execute both `k_offer` and a separately
restored copy of `I`. Instead, a finite continuation slot denotes the opaque
source continuation `k_offer = I(k0)` together with an observational summary
of the inner context already composed into it. For a fixed source program and
`K`, a slot may hold a finite set of records:

```text
KontFact = (Raw | Forwarded,
            continuation_slot | UnknownKont,
            captured_handler_ref | UnknownRef,
            αK(inner_scope_snapshot),
            bounded_lineage_and_grants,
            offer_summary ∈ P(ReqFact) | TopOffers)
```

`inner_scope_snapshot` is evidence for classifying offers made while the
opaque continuation runs; it is not executable a second time. Raw invocation
transfers through the continuation slot under the outer context, with `H`
absent. Forwarded invocation transfers through the stored `H(k_offer)` wrapper
under the outer context, retaining the captured semantic activation of `H`.
Both clone the immutable fact for each invocation. “Apply `I` once” here means
that its transformer is represented once in the slot summary; it does not
limit how many times an inner operation arm may invoke its own underlying
continuation.

Joins union whole facts. Allocation-site slots and the bounded stack carrier
make the record set finite, but a join that merges distinct dynamic
activations must union their possible scope classes and erase any grant proof
that does not hold for every represented identity. A truncated snapshot,
unknown slot, lost wrapper, or ambiguous captured handler must degrade to
`UnknownKont`, not merely set the scope field to `Unknown`.
`UnknownKont` has a top control summary: it may return, offer every family in
the finite `Fam` universe with `UnknownOp`/`UnknownOrigin`/`UnknownMask`,
execute any relevant handler arm, and re-enter any captured wrapper. This
fallback may make many drops impossible, but cannot hide an offer or arm
effect. If `Fam` is not closed over the source and imported interfaces, extend
it with an explicit `UnknownFam` that also prevents subtraction. Every family
in a continuation effect bound must couple to a concrete offer fact or this
unknown summary; unknown continuation control cannot be treated as an empty
offer set. `TopOffers` ranges over finite operation/family labels, source
origins, scope classes, and handler/arm slots (with explicit `Unknown*`
members). When a captured-wrapper reference is lost, install that top summary
at every possibly affected static handler slot, conservatively all slots if
the affected set is unknown; do not omit a destination because its dynamic
activation identity was lost. This makes the fallback finite while ensuring
the observation invariant sees every possible handler destination.

The need for a control summary is visible in a forwarded-resume trace. Let
`C0 = Request(u, (), λ_. Request(p, (), λ_. Return(0)))`; inner handler `I`
forwards `u` and handles `p` with an arm that requests `g`; outer handler `H`
forwards `u` and handles `g`. If an outer context resumes `u`, the required
suffix is `H(I(k0))`, so the `g` request is offered to `H`. Replacing a lost
`I` summary with only `H(k0)` omits that offer. A scope-only `Unknown` would
not repair the missing control path. `UnknownKont` must instead include the
possible `g` offer (or top offers), and row/provenance coupling must ensure
the family cannot be subtracted vacuously.

An independent compiler-referee delta review confirms this top-control fallback
closes the lost-`I` omission at the candidate level and does not introduce exact
continuation inference or usage tracking. The review's remaining finite-domain
clarification is now stated explicitly: a lost wrapper fans top offers out to
every possibly affected handler slot. The continuation-slot completeness,
top-control simulation, and row-to-offer coupling are still unproved.

#### Top-control closure lemma target

The most conservative `UnknownKont` case can be made explicit without
simulating the lost continuation's control structure. Define a finite
abstraction of the checked module and imported interfaces: handler, arm,
continuation, value/thunk, operation, family, origin, and boundary slots are
finite, with explicit unknown members. `ReqFact` and bounded lineage use the
finite domains already described above. `TopKont` is a symbolic absorbing
element, not an enumeration of every boundary map. Its concretization includes
all request facts at every local handler slot; every finite map from boundary
occurrences to subsets of `AbstractScopeClass`; all local continuation, arm, value,
and thunk destinations; every return/request/forward/handle/resume outcome;
and top latent effect `⊤Eff`. An `UnknownHandler` or `UnknownArm` interface
destination contributes the same top summary at every compatible local
handler slot.

For a concrete observation, project its dynamic handler identity to the
corresponding static handler slot, or `UnknownHandler` when unavailable.
Project each dynamic boundary identity to its static boundary occurrence and
union possible `AbstractScopeClass` values per occurrence. Repeated dynamic instances
at one site remain separate bounded-lineage entries while represented; if
truncation or a join loses that distinction, widen the affected occurrence to
all scope classes and `UnknownMask` instead of overwriting one instance with
another. The `Drop` test remains universal over every fact and every class in
these projected sets.

`⊤Eff` denotes every concrete effect row, including families omitted from the
current finite labels and future instantiations of open imported rows. It is
not an ordinary fresh family label: a closed annotation accepts `⊤Eff` only if
that annotation also denotes top or a separate proof narrows the unknown
family set. Otherwise the annotation check fails conservatively. Every
`TopKont` includes observations with `InsideDenied` and `Unknown` for every
boundary; because `Drop` quantifies over all observations, no represented
family can be subtracted. For this fallback, `⊤Eff \ Drop = ⊤Eff` unless a
separate proof first narrows the unknown family set. Any result that may
capture the lost continuation propagates `TopKont` into its value/thunk slot
as top latent effect and provenance. If capture cannot be ruled out, use
`UnknownValue` with that top summary. Return, storage, ordinary call, force,
closure escape/re-entry, arm entry/exit, scheme instantiation, and wrapper
resumption all preserve or widen `TopKont`; none may clear it by leaving the
current stack. Top request observations fan out to every possibly affected
local handler slot, and an unknown external handler destination widens to the
top interface summary.

The finite-slot closure premise is that every concrete observation and
destination from the checked source and imported interfaces either maps into
these slots or maps to an `Unknown*` slot whose top row/observation semantics
is as above. Given that concretization invariant and the row-to-offer coupling,
every concrete request in a lost continuation is represented, each arm/call/
resume destination is covered, and each emitted effect is below `⊤Eff`.
Because every listed transition preserves the symbolic top, induction over
finite trace prefixes proves observation coverage and effect inclusion after
loss, including requests emitted by an inner handler arm and requests reached
after a stored continuation is forced or called. This is a fallback soundness
lemma only; it neither proves the precise continuation-slot transfers nor
yields useful principal rows for paths that reach `TopKont`.

This closure does not require a continuation-use count. It may retain every
effect or reject source annotations that a more precise analysis or Oracle
accepts. This is a candidate precision cost, not a selected compatibility
difference: any concrete Oracle mismatch must still be exhibited and recorded
before choosing the fallback for the supported envelope.

#### Concrete-to-abstract relation for the top fallback

For the fallback proof only, write a concrete source configuration as
`κ = (D, L, Env, ctl)`: `D` is the ordered word of live dynamic delimiter
instances, `L` is ordered request-boundary lineage, `Env` contains every
reachable local, stored, exported, and imported value root (including
closures, thunks, and captured continuations), and `ctl` is the current
return/request/arm/call/force/resume control point plus pending wrappers.
Continuation values denote the source `k_offer` closures, including their
already-composed handler transformers; they are not reduced to raw stack
slices.

An abstract state `A` contains finite sets of projected stack and lineage
facts, a finite set of abstract control facts, a finite map from static
value/allocation slots to sets of value facts, a map from static handler slots
to offered `ReqFact` plus scope relations, and effect bounds for each static
effect slot. A control fact names a control slot or `UnknownControl`, plus any
pending continuation kind and wrapper references. `TopControl` denotes all
control slots and pending wrappers and necessarily carries `TopKont`, `⊤Eff`,
and top request observations at every possible handler destination. A value
fact contains its value kind, latent row (possibly `⊤Eff`), and any captured
continuation summary.
Define `κ ∈ γ(A)` when all of the following hold:

1. `αK(D)` and the bounded projection of `L` occur in the corresponding
   abstract stack/lineage alternatives.
2. Every concrete environment value maps to a static value slot whose fact
   covers its kind, latent effects, and captured scope/continuation evidence.
3. Every concrete request offered to a dynamic handler maps to that handler's
   static slot (or `UnknownHandler`) and to a fact whose family, operation,
   origin, and ordered lineage cover the concrete request, and whose
   `γscope` for each corresponding boundary occurrence contains the concrete
   relation. Every independently active eligibility mask is represented in
   `may_blockers` or by `UnknownMask`; this includes non-boundary provider
   guards. Dynamic boundary instances at one site keep distinct bounded
   occurrence positions; if a projection merges them, the union must contain
   every concrete class and include `UnknownMask` where identity is lost.
4. Every concrete immediate and latent effect is included in its abstract row.
5. The current `ctl` and all pending wrappers/continuations map to an abstract
   control fact. Unknown control identity maps to `UnknownControl`/`TopControl`;
   pending lost wrapper identity maps to `UnknownRef` with top control. Any
   `TopControl` fact carries the top effect/provenance/offer summary above; it
   cannot exist as an untainted control-only marker.
6. For every family in a scrutinee effect bound, its contribution is
   classified by route: a current or forwarded route to a handler is covered
   by an offer fact at every possibly receiving slot; a route confined to a
   matched raw continuation is preserved in that continuation's latent effect
   and the arm/value slot that invokes or exports it; an unresolved or mixed
   route retains all possibilities or widens to unknown. For `⊤Eff`, all
   effect, continuation, offer, and compatible interface destinations are top.

The projection of a dynamic handler or boundary identity to a static site is
only a carrier for a *set* of possible dynamic instances; it is never an
identity proof. A concrete `InsideGranted` classification enters the abstract
scope set only when the exact live activation and family grant are established.
Otherwise the set includes `InsideDenied` or `Unknown` as appropriate. Join is
union of whole abstract alternatives; if value/environment correlation is
lost, the product admits extra states, and their scope classes/effects must be
included rather than reconstructed from source-site equality.

Define `step#(A)` as a set of pairs `(A', Obs#)`, where `Obs#` is the set of
request offers emitted on that abstract edge. The top-taint predicate for an
abstract edge holds when its control point, a pending wrapper, or a value used
by the edge is represented by `TopControl`, `TopKont`, or `UnknownValue`.
An abstract observation is a tuple `(handler_slot, operation, family,
origin, bounded_lineage, scope_relation, may_blockers)` over the finite domains
above. `may_blockers` ranges over subsets of finite boundary and active-mask
slots plus `UnknownMask`.
Define `CoverObs(o, ô)` componentwise: dynamic handlers, operations, families,
origins, and lineage in concrete offer `o` map to their exact abstract labels
or the corresponding `Unknown*` label, each concrete boundary class in `o`
belongs to `γscope(S)` for the corresponding abstract scope set `S` in `ô`,
and every concrete active blocker in `o` is represented in `may_blockers` or
by `UnknownMask`. This is a coverage relation, not a unique projection:
identity loss may admit several covering tuples. `UnknownHandler`, `UnknownOp`,
`UnknownOrigin`, and `UnknownFam` cover every concrete identity outside the
finite exact-label set; `UnknownFam` denotes row top, not a standalone family
that a closed row can accidentally ignore. `TopObs` is the set of every
abstract tuple, including tuples with every possible scope relation and
blocker set, so for
every concrete offer `o` some `ô ∈ TopObs` satisfies `CoverObs(o, ô)`.
The top-edge simulation goal is: if `κ ∈ γ(A)`, `κ →[Obs] κ'`, and that edge
uses top-tainted control/value, then some `(A', Obs#) ∈ step#(A)` satisfies
`κ' ∈ γ(A')` and, for every concrete offer `o ∈ Obs`, some `ô ∈ Obs#`
satisfies `CoverObs(o, ô)`. Silent edges have empty `Obs`. This labelled-edge condition covers
requests that are handled and disappear before the successor state.

When the top-taint predicate holds, `step#` preserves or widens the complete
top summary across each control and value transition:

| Concrete transition | Required abstract transfer when the full top summary is present |
|---|---|
| A request is offered, then matched or forwarded | Before either branch, put every possible `TopObs(handler, operation, family, origin, lineage, scope, blockers)` in `Obs#` for all local/unknown handler destinations; retain `TopKont`/`⊤Eff` in the successor. A fact stored only in `A'` does not cover an offer handled on this edge. |
| Catch entry/exit, arm entry/exit | Retain `TopKont`/`⊤Eff` and fan top request, scope, and blocker facts to every possible handler slot. |
| Raw or forwarded continuation resume | Preserve top on the continuation slot; forwarded resume additionally retains the captured `H` wrapper possibility. |
| Return, closure/thunk construction, storage, or escape | Copy top latent row and top provenance to every result slot that may capture the continuation; otherwise use `UnknownValue`. |
| Call, force, or recursive re-entry | Load the top value summary and emit top observations under every possible current handler slot. |
| Scheme instantiation or imported call | Do not freshen away top; instantiate/export `⊤Eff` and top provenance, or widen to `Unknown*`. |

This transfer table is sufficient for top-tainted edges if the concretization
and finite-interface premises hold: the next concrete control point, reachable
value, request observation, and effect all lie in the top summary. Induction
over finite labelled paths proves `γ` coverage for executions after loss; it
does not prove how a non-top `KontFact` is computed or when it must widen.
Escaped roots and imported open rows are part of the induction, not separate
post-processing.

#### Finite-carrier proposition

For one fixed finite checked source and finite interface declarations, fix
finite sets of handler, arm, continuation, value/thunk allocation, operation,
family, origin, boundary, control, and effect slots. Open or unenumerated
imported families map to `UnknownFam`/`⊤Eff`; unenumerated interface
destinations map to the corresponding `Unknown*` slot. Fix `K < ∞` for the
bounded stack and lineage suffixes. Then the abstract carrier described above
is finite:

- The stack and lineage domains are bounded words over a finite tag set, a
  saturated prefix count `{Zero, One, Many}`, and a subset of finite prefix
  tags. Their powersets are finite.
- `ReqFact` is a product of finite operation/family/origin labels and a subset
  of finite blocker labels. `KontFact` is a product of finite mode, slot,
  handler-reference, bounded-snapshot, bounded-lineage, and
  `P(ReqFact) ∪ {TopOffers}` components. Their powersets are finite.
- Value facts are drawn from finite value kinds, latent-row values
  `P(Fam) ∪ {⊤Eff}`, and finite continuation references. The environment is a
  finite map from static value slots to subsets of these facts; it therefore
  forgets dynamic multiplicity and joins repeated instances at their static
  allocation slot.
- Effect maps, control facts, and edge observations are finite products or
  powersets over the declared finite slots and labels. `TopKont`, `TopControl`,
  and unknown interface labels are symbolic elements of these finite domains,
  not generators of fresh identities.

Thus the full abstract state space is a finite product of finite powersets for
fixed source/interface inputs and `K`. This establishes carrier finiteness only.
It does not establish that every concrete source configuration projects into
the stated slots, that a joined environment preserves enough correlation for
`Drop`, or that any abstract transfer simulates a concrete step. Those require
the coverage and transition proofs above; finiteness by itself proves neither
soundness nor useful acceptance precision.

A focused compiler-referee delta review found no finding in this finite-carrier
argument under its fixed finite-slot and fixed-`K` premises. The review checked
that each stated component is finite and that recursive/dynamic identities are
represented by finite slots or explicit unknown elements. It did not review or
establish concrete slot coverage, sound transfer, provider eligibility, or
acceptance precision.

Review closure: the first version omitted top propagation through escaped
values and treated a fresh unknown-family token as though it bounded omitted
families. Architect and compiler-referee review identified those gaps. A
focused compiler-referee delta review confirms the revised absorbing
`TopKont`, value taint, handler/boundary projection, universal `Drop` check,
and row-level `⊤Eff` close them at the candidate-lemma level. The explicit law
`⊤Eff \ Drop = ⊤Eff` was added after that review from its minor clarification.
Subsequent independent review found that the first γ relation omitted control
and pending wrappers, treated `Unknown` as a concrete singleton, allowed
`TopControl` without a top effect summary, and did not require an edge
observation when a request was handled and vanished. The candidate now maps
control/wrappers and all reachable roots, gives `Unknown` its full-class
concretization, ties `TopControl` to top row/offers, and emits `TopObs` before
either match or forward. A focused compiler-referee delta review closed these
findings at the candidate level. A second focused delta review confirms the
`TopObs` schema matches the emitted edge observations; this note now states a
set-valued `CoverObs` relation so `γscope` is not mistaken for a unique
projection. The formal full-language concretization, transition simulation,
and annotation-solver integration remain unproved.

At each offer of a request to a dynamic activation `h`, emit an observation
`(operation, family, origin, ordered lineage, h, active-scope relation)` before
the branch. `Eligible(q,h,κ)` remains a parameterized source predicate; this
machine does not select wildcard/omission behavior, expiry semantics, or an
Oracle guard rule. The bounded abstraction must carry the continuation kind
and paired scope/provenance snapshot together. It must never restore `h` from a
matching static site or reused stack position. A stack-machine encoding must
prove that its operational frames correspond to the handler transformations
already represented by `k_offer`; it cannot both run a transformed
continuation and separately reinstall those frames. If unwind crosses more
than `K` frames or a join loses the snapshot identity, use `Unknown`.

The key compositional lemma is conditional: if initial configurations are
covered, each transition above is simulated by the bounded abstract transfer,
and every concrete offer observation appears in the abstract observation set
with all concrete scope classes, then induction over finite trace prefixes
covers every request in `Offered(H,C)`, including every outer-resume branch.
Exact operation coverage plus the universal scope-class test then makes
`Drop(H)` sound. Matched raw-`k` suffixes remain accounted for by the arm's
`k : May(C)` bound, while forwarded suffixes are inspected again under the
restored `h`. This reduces the general handler proof to transition simulation,
observation refinement, and row/provenance coupling; it does not prove those
premises or infer continuation usage.

The bounded machine encoding of the `I` segment and observation refinement
remain proof obligations. In particular, a same-site activation may be
suspended while another activation at that site is entered; the saved dynamic
`h` must be restored without merging it with the newer activation. The source
request-tree equation is the reference: unmatched inner handlers are already
composed into `k_offer`, and forwarding through `H` composes `H` exactly once.
The finite continuation-summary proposal narrows the open implementation of
that equation, but the top-control fallback, completeness of continuation-slot
summaries, and row-to-offer coupling still need proof.

Review closure: an independent compiler-referee initially found ambiguity
between `k` and the inner segment `I`, plus missing distinct return
destinations. The candidate now makes `k_offer` the already-transformed
continuation, keeps `ScopeSnap` non-executable, specifies forwarding as
`Request(q, x -> H(k_offer(x)))`, and states raw versus forwarded return
behavior separately. A focused delta review checked a nested inner handler
whose value arm changes the result and closed both findings. An independent
architect review found no conflict with the precision/principality decision:
the trace model remains a soundness reference, while `May(C)` may conservatively
over-approximate and the leastness claim remains relative to the chosen
compositional abstraction. This closes only the source request-tree wording;
the bounded-machine encoding of `I`, observation refinement, and full
simulation remain open.

The target step-simulation obligation is:

```text
α(step(κ)) ⊑ step#(α(κ))
```

for every concrete source-semantics step, including call/return, force,
closure escape/re-entry, scheme instantiation, handler arm entry/exit,
forwarded resumption, and multi-shot continuation invocation. Forwarded
resumption restores its captured handler context; matched raw `k` does not
automatically restore the matching shallow handler. Multiple resumes join
their abstract outcomes and require no usage count. A row/provenance coupling
lemma must additionally partition each family contribution by route. A
contribution that may be offered to `H` maps to a represented request fact or
`Unknown`; a contribution confined to a matched raw continuation is instead
preserved through `k`'s latent effect and the arm/value effect if invoked or
exported. If paths are joined or the route is unknown, represent every
possible route or widen to `Unknown`. Step simulation alone does not justify
`Drop`; also
prove the following observation/refinement invariant, including at the initial
state:

1. Every concrete request `q` offered to dynamic handler `H` has a covering
   abstract request fact at the corresponding static handler slot.
2. For every receiving-boundary identity on `q`'s concrete lineage, that
   fact's `γscope` contains the concrete relation for this exact
   `(H,q,boundary)` activation tuple. Every other active mask that can
   independently deny `H` is represented in `may_blockers` or by
   `UnknownMask`; omission is never interpreted as proof of absence.
3. Per-concrete-pair classification is sound, and exact operation coverage is
   checked separately. `Drop` requires `γscope(S) ⊆ {Outside, InsideGranted}`
   for every receiving boundary and no unresolved `may_blockers`; a non-boundary
   mask can be discharged only by a matching grant proved in scope for this
   handler/request. Any concrete `InsideDenied` possibility, `Unknown` whose
   concretization includes it, or `UnknownMask` prevents `Drop`; a joined
   `{Outside, InsideDenied}` cannot pass just because one possibility is
   outside.
4. Closure/thunk/continuation summaries preserve latent effect rows, scope
   relations, and blocker evidence. Boundary expiry means `Outside` only after
   proving the source semantics cannot restore that receiving scope through a
   carried value; a lexical return or stack pop alone is insufficient.

Then every family admitted to `Drop(H)` is covered and eligible for every
concrete request represented by its abstract facts. Without this implication,
the abstract scope test is not a sound subtraction certificate.

This is not yet a finite-quotient theorem. The concrete activation semantics,
abstract join/transfer soundness, and effect of truncation on the supported
final-acceptance envelope all remain open. Recursive or escaped-callback
cases may become `Unknown` and therefore lose acceptance precision. No value
of `K` is selected. Any useful precision/acceptance claim requires explicit
fixtures and proof over the resulting abstraction; exact trace support remains
the soundness reference, not a continuation-usage inference requirement.

Concrete callback annotations are part of the fixed source-contract input and
can change `Drop` and therefore `F`; this theorem compares solutions only for
the same annotated program. Concrete result annotations are separate upper
filter checks `ρ(slot) ≤ U`, not operations that clip or alter `F`.

Under monotonicity, the finite lattice gives a least fixed point
`lfp(F) = ⋁ₙ Fⁿ(⊥)`, with iteration reaching stability after finitely many
strict increases. For every `ρ ∈ Sol(F)`, `lfp(F) ≤ ρ`; therefore, if any
solution satisfies a separate concrete result filter `ρ(slot) ≤ U`, the least solution
satisfies it too. This establishes principality only if derivations
of the selected effect core are exactly characterized by `Sol(F)` and its
separate filters. Principality here means least derivable `D_eff` bounds for
this effect core. It does not mean least exact trace support, and it does
not establish principal value types, higher-order subtyping, scheme/SCC
generalization, or final program acceptance for the full language. If the
request-configuration summary is coarse, the result may retain extra families
and lose acceptance precision; soundness additionally requires complete
configuration coverage, correct eligibility, sound transfer simulation, and
latent-effect preservation.

A focused compiler-referee delta review confirmed the `D_eff` lattice,
monotonicity of fixed-`Drop` removal, compatibility with unsubtractable
`⊤Eff`, and the finite Kleene least-solution argument. This result is
conditional on `F` using only the stated monotone transfers and on derivations
matching its pre-fixed solutions. It does not prove that dynamic origins yield
a fixed sound `Drop`, that source rules generate exactly `F`, or that the
full-language source/runtime system satisfies these conditions.

This fixed-point argument is a proof target, not yet a theorem for the current
candidate: source-origin completeness, handler-scope stability, and the full
construct interpretation still require proof and independent review.

## Worked least bounds for the shallow witnesses

Take `Fam = {choose}`, one fixed handler activation, and a closed direct
request tree with no other effects. For both one-request cases, and for the
first request of the two-request case, every request offered to the handler is
covered and eligible, so `Drop = {choose}`. The second request in the
two-request case is in the raw continuation: it does not reach this handler,
but invoking `k` has latent bound `E = {choose}`, so the arm bound restores
`choose`. In the final case a reachable, uncovered `choose` operation is
offered to the handler, so `Drop = ∅`. Each scrutinee has bound
`E = {choose}`.

| Witness | Exact trace support after the catch | `Drop` | Arm bound with `k : E` | Candidate result `(E \ Drop) ∪ arms` | Least row |
|---|---:|---:|---:|---:|---:|
| One request, arm ignores `k` | `∅` | `{choose}` | `∅` | `∅` | `∅` |
| One request, arm invokes `k` once | `∅` | `{choose}` | `{choose}` | `{choose}` | `{choose}` |
| Two requests, arm resumes first request | `{choose}` | `{choose}` | `{choose}` | `{choose}` | `{choose}` |
| Reachable uncovered `choose` operation | `{choose}` | `∅` | `∅` | `{choose}` | `{choose}` |

In the non-resuming case, merely giving `k` latent bound `E` adds no effect;
ordinary application contributes `E` only when the arm invokes it. In the
one-request resuming case, the abstract least bound intentionally retains
`choose` although the exact suffix is pure. In the two-request case that same
bound also covers the second request that escapes shallow resumption. The
last row illustrates that an uncovered reachable operation contributing to
`E` prevents family subtraction; an omitted operation that cannot occur does
not. These equations establish leastness for the fixed
one-family witnesses under the candidate transfer rules; they do not prove
that source lowering, provider analysis, or the general constraint operator
meets those rules.

## Adversarial review result

Independent architect and compiler-referee reviews agree on the following:

- **Blocking for a general rule:** define provider identity and handler
  eligibility independently of family labels. The candidate now separates
  request provenance, ordered boundary instances, handler activations, and
  grants; a family may be removed only when every reachable configuration is
  covered and eligible, otherwise retain it conservatively. The activation
  transport and source/runtime correspondence remain unproved.
- **Major, narrowed:** the finite-core candidate now states principality as
  leastness among pre-fixed solutions of explicit compositional lower-bound
  constraints, with result filters checked separately. Independent review
  confirms the finite-lattice step under those premises. A finite powerset
  codomain alone is insufficient: derivation correspondence, complete dynamic
  origin summaries, higher-order subtyping, SCC schemes, and final acceptance
  remain outside the proved result.
- **Major:** incomplete handlers and residual operations must remain in the
  bound. Non-resumption removes a family only under complete eligible
  coverage. Nested outer handlers and callback ownership need explicit rules.
- No direct-fragment counterexample was found to the whole-scrutinee `k`
  effect, provided ordinary application and escaped closures preserve latent
  effects. This is review evidence, not a completed proof.

## Next characterization and proof matrix

Before considering any weight representation, define and prove the
provider/capture eligibility judgment, then check the effect abstraction
against:

- one request with resume, two sequential requests with resume, and no resume;
- complete coverage, an incomplete family handler, and one uncovered
  operation in an otherwise handled family;
- nested handlers with distinct and repeated families;
- outer-owned versus inner-owned callback under a same-family inner handler;
- delayed thunk forced under a handler;
- repeated callback calls sharing one frame pop;
- residual effects that are passed through and later handled by an outer
  eligible handler.

Only after this matrix should a weight be assigned a denotation. Every proposed
left/right transfer then needs a preservation argument against this abstract
judgment. Method selection, roles, and implementation resolution stay in the
mandatory later gate from the redesign charter unless this proof exposes a
concrete dependency.

No implementation, Oracle weight rule, or equivalence claim is authorized by
this candidate.

## Provider/capture eligibility remains open

The frozen reference directly states these principles:

- callback-origin effects supplied by an outer caller are protected from an
  inner same-family handler unless the receiving boundary exposes them;
- a concrete callback argument row grants matching-family visibility to
  handlers inside that receiving function;
- wildcard surface rows do not erase unrelated hygiene evidence; and
- a shallow operation arm receives the raw continuation.

The nested-provider probes in
`2026-09-30-intrusion-weight-routing-counterexample-search.md` characterize the
first two behaviors as outer result `[1]` without the concrete contract and
inner result `[2]` with `[choose]`. The helper witness records a further Oracle
conflict: its pure `invoke` scheme drops an effect that its callback call can
perform. The successor must propagate that effect and conservatively retain it
when shallow resumption can reach another request. These observations do not
define a provider identity or grant lifetime.

A source semantics will need at least distinct operation-family, request
provenance, callback-boundary, and active-handler identities. Candidate
eligibility notation is:

```text
eligible(request, handler) iff
    handler is active
    and handler covers request.operation
    and visibility evidence authorizes this request at this activation
```

The last condition is intentionally unspecified. Treating a capture contract
as a transferable Boolean attached to a family is unsafe: if that bit escapes
in a returned closure, it could authorize an unrelated inner handler outside
the introducing receiving scope. The converse shortcut—dropping every grant
at a helper return—could prevent an explicitly permitted nested handler from
working. The evidence must therefore be scoped to its introducing boundary
and active handler, and its call, force, closure-escape, and scheme-instantiation
transport must be proved without widening its scope. This is a challenge
example, not an established Oracle behavior or a selected successor rule.

Annotation syntax also cannot be collapsed to one “has a contract” bit.
Absent annotations, concrete nonempty rows, concrete empty rows, wildcard
`[_]`, and any effect-only skeleton position with wildcard behavior may impose
different constraints. The frozen effect specification characterizes several
of these paths, while its weight operations remain non-authoritative. The
successor must define the semantic meaning of each supported annotation form
before deriving any encoding.

Independent architect, compiler-referee, and spec-auditor reviews agree that
provider provenance must remain separate from family identity and that the
family-removal side condition must quantify over every possible request path:
each contributing operation must be covered and eligible at the handler
activation being modeled. The references establish the visibility principle,
not the provenance assignment, grant lifetime, closure-escape rule, or
inference/runtime correspondence theorem. Consequently, the notation above is
only a proof target. It does not close the blocker or authorize a data
representation.

The next proof artifact should define a source request-tree judgment with this
eligibility relation and prove a one-step handler simulation: covered eligible
requests enter the matching arm; incomplete, uncovered, or ineligible requests
forward with provenance intact; and any raw-continuation resumption preserves
the whole pre-handler effect bound. Include the callback/hygiene pair,
helper-call composition, delayed thunk force, closure escape, and repeated
callback request before relating the judgment to a runtime representation or
weight calculation.

### Candidate provenance relation (unselected)

A useful proof target keeps these identities separate:

```text
request q = (operation, family, origin, ordered_boundary_lineage)
handler h = (activation_id, covered_operations)
grant g = (introducing_boundary, family_set, scope)
```

`family` here is a typed family identity, including its invariant arguments,
not just a path/name. A grant for `F<Int>` cannot authorize `F<String>` by
path equality. Scheme instantiation must transport grant arguments with the
same binder substitution used for the callback effect occurrence; the exact
successor binder ownership and transport proof remain open.

A source-grounded candidate eligibility clause can be stated as:

```text
eligible(q, h) iff
    active(h)
    and exact_operation_covered(h, q.operation)
    and for every boundary b in q.ordered_boundary_lineage:
          outside(h, b) or matching_grant(b, q.family, h)
    and no_other_active_or_carried_boundary_masks(q, h)
```

`outside(h,b)` means handler activation `h` is not dynamically nested within
the particular receiving activation represented by boundary instance `b`.
It is activation-specific, not a lexical test on where a closure was created.
A crossed callback boundary does not by itself block an outer handler.
`matching_grant` requires an explicit contract at that boundary for the family
and a scope proof that includes this activation. How this receiving scope is
represented and transported across closure re-entry remains a proof
obligation. Other active guards may also mask a request even when the handler
is outside this grant scope. Thus the escaped-callback
inference is conditional: the caller may handle the request if its exact arm
matches, it is outside the maker grant scope, no other carried/active boundary
masks it, and the source/runtime correspondence preserves that eligibility.
This clause is a source-grounded candidate, not a selected successor rule.

An unresolved carried marker is a possible mask and therefore cannot be
discarded merely because the original receiving activation has returned. The
relation must say whether a carried marker reactivates on closure invocation,
force, or projection, and which dynamic handler identities it can protect. Until
that is specified, the escaped request remains ineligible for subtraction in
the proof abstraction (its family stays in the outward bound). This is a
conservative unknown case, not a decision that every marker remains active.

The eligibility judgment must require an active handler, exact operation-arm
coverage, and a derivation that every callback boundary on the request's path
to that handler permits this family at this activation. Family equality alone
cannot discharge the last premise. A request with no callback boundary uses
the direct shallow rule. Handler subtraction is allowed only if this judgment
holds for every reachable request contributing that family, including each
suffix reached by resuming a forwarded continuation. The lineage is an ordered
sequence of boundary instances, not a set: repeated pushes, re-entry, and one
shared pop must retain their order and multiplicity until a preservation
theorem justifies normalization.

The frozen source documentation motivates, but does not complete, a candidate
grant rule: a concrete callback argument contract exposes its listed families
to handlers inside its receiving function. The candidate should identify the
receiving activation and handler activations explicitly; it must not turn the
grant into a family-wide Boolean. Passing the callback through a helper must
preserve its origin and boundary lineage. A returned closure must preserve its
latent effect and provenance. A source-grounded scope hypothesis is that the
grant authorizes matching handlers inside the receiving function activation;
it is not a transferable permission for unrelated later handlers. Thus the
`caller` catch in the `maker` closure probe is outside `maker` and need not
inherit `maker`'s grant to handle a request that escapes the returned closure,
provided no other active boundary masks it. The marker spec's own-family
`add_id` rule is compatible with this interpretation at that boundary, but
does not establish eligibility at a later caller activation. The no-contract
outer-handler control is also only adjacent evidence; it does not prove the
concrete-contract closure-return path. This escaped-closure conclusion is an
inference, not an explicit frozen source rule. Formal activation scope,
helper composition, and the relation between returned-value markers and
handler eligibility still need proof. They must not be inferred from
`StackWeight` or runtime marker code; that code conflicts with the marker spec
on own-path coloring.

Until those scope rules are proved, the conservative effect abstraction
retains the family whenever eligibility is unknown. This is compatible with
the user's precision decision: the bound may over-approximate exact trace
support, while its principal-solution theorem is stated over the chosen
compositional abstraction. The following annotation forms remain distinct
proof cases: absent callback annotation, concrete nonempty row, concrete empty
row, wildcard row, and result-position filter. Frozen documentation describes
different roles for these forms, but their successor grant and filter
semantics have not been selected. This relation is only a proof target and
does not resolve the frozen marker code/spec conflict.

The frozen contract-metadata design sharpens this distinction: only concrete
heads in root function-parameter annotations generate argument-contract
markers; wildcard and row tails do not. A root computation annotation is a
separate static subtraction contract, not argument metadata. The frozen effect
reference describes a result-position concrete row as a static escape filter.
These are representation/lowering facts, not authority for successor weight
semantics. See
`/tmp/yulang-intrusion-oracle/notes/design/2026-06-24-explicit-effect-contract-metadata.md:65-81,111-128`,
`/tmp/yulang-intrusion-oracle/web/docs/reference/effects.md:243-263`, and
`/tmp/yulang-intrusion-oracle/spec/2026-05-31-effect-variable-subtractable.md:254-274`.

### Frozen-Oracle closure-escape probe

A new source characterization tests callback effect transport through a
returned closure:

```yu
act choose:
  our reject: () -> int

my rejecter() = choose::reject()
my maker(f: () -> [choose] int) = \_ -> f()
my delayed = maker(rejecter)
my caller(): [] int = catch delayed(0):
  choose::reject(), k -> k 3
  v -> v

caller()
```

The frozen Oracle `check` accepts this program. Its `--poly-raw` dump gives
`maker`'s returned function, `delayed`, and `caller` pure (`Bot`) return-effect
slots. Both interpreter and evidence VM instead report an unhandled
`choose::reject`. Thus callback effect information is lost across this
closure-return path before the pure caller annotation is checked. The
successor's sound effect abstraction must retain `choose` in the returned
function's latent effect. Handler eligibility for the escaped request remains
open, but the current coarse whole-scrutinee continuation candidate predicts
that the explicit `[]` annotation is rejected either way: if the handler is
ineligible, the scrutinee effect remains; if eligible, invoking `k` contributes
the whole pre-handler effect through the unfiltered arm. The derivation and
compatibility consequence are stated below. The Oracle accepts the annotation
while both runtimes leave the request unhandled; this is a concrete
accepted-but-failing Oracle case, not yet a selected successor rule.

A direct-closure control with `delayed = \_ -> choose::reject()` retains
`[choose]` in the delayed function and caller schemes; the inferred caller
returns `3`, while an explicit pure annotation is rejected with an effect
filter mismatch. The contrast localizes the missing static effect to the
callback/closure transport path. It does not decide whether the callback's
later request is eligible for the caller catch; the minimum successor rule is
that it cannot be erased from the returned function's effect.

The same source was checked with the `maker` callback contract changed while
the pure caller annotation was removed. With no contract, wildcard `[_]`, and
concrete empty `[]`, each inferred `caller` retains `[choose]`, and the
interpreter's caller handler returns `[3]`. With concrete `[choose]`, the
inferred `maker` result, `delayed`, and `caller` instead have `Bot` return
effects, and both runtimes report unhandled `choose::reject`. Thus these
annotation forms differ on this exact closure-escape path. The annotation-
dependent effect loss is consistent with the concrete capture grant affecting
analysis beyond the receiving function's inner handlers, but does not
establish the Oracle mechanism or a general grant-lifetime rule. The successor
must preserve the unconsumed callback effect in the returned closure; capture
evidence transport across returned functions remains open. Frozen runtime
guard notes describe result-marker propagation across returned functions, so
an unconditional rule that closes every grant at function return would be
premature. A source-derived symbolic marker trace for the returning-callback
control is recorded below; it characterizes frozen implementation code but
does not choose the successor's boundary rule.

The frozen runtime IR narrows the mechanism without settling the source rule.
The concrete-contract variant lowers the callback argument with
`arg[add_id[1, choose, own, resume-own]]`; the returned closure's maker adapter
has `body[add_id[1, choose, own]]`. At the caller, the concrete variant has a
plain `catch (delayed 0)`, while the absent, wildcard, and concrete-empty
variants retain a `thunk[[choose], int]` and lower to a marked
`catch marker[choose](force-thunk ...)`. These are compiler-lowered marker
plans, not an instrumented trace of runtime `GuardId` values. The frozen
runtime rules say returned functions carry markers and later calls re-enter
their marker frame; the concrete variant's two runtimes report the resulting
request unhandled. This shows that effect-row erasure and runtime marker
routing coexist in this case, but does not prove whether the caller handler is
eligible in the successor's declarative semantics.

The frozen runtime source gives a conditional route derivation for the plain
caller catch, but its own-path coloring condition conflicts with the frozen
runtime marker specification. The implementation's `mark_request` path can,
under its `guard_own_path` condition, record a guard and `CarriedGuard`
exposure snapshot for an own-path request; adapter marker frames then pop
while `guard_ids` and `carried_guards` remain on the forwarded request. A
plain `Catch` adds no handler frame, and the missing-handler route can use a
carried guard to skip its arm. However, the frozen marker specification says
that `add_id[0,path,id]` colors a request only when the marker path is not a
prefix of the request path; it therefore requires an own-path request to
remain readable at that boundary. The code-derived route is characterization
of the frozen implementation and a code/spec conflict, not a normative rule
for the successor. It needs an approved specification resolution before any
semantic adoption. The relevant implementation rules are in
`crates/mono-runtime/src/lib.rs:471-484`,
`crates/mono-runtime/src/runtime/flow.rs:135-180,296-376,391-412,438-553`,
and `crates/mono-runtime/src/runtime/eval.rs:360-380,449-477` in the frozen
checkout; the conflicting path-prefix condition is in
`spec/2026-06-13-runtime-guard-markers.md:117-130`. A source-derived symbolic
execution of the nested adapter/value-marker composition is recorded below,
but no dynamic request-state instrumentation was performed. The exact
implementation route does not resolve the normative code/spec conflict or
define successor source semantics.

The source-derived allocation trace accounts for adapter calls during
top-level `m0`: A (the outer `m0` adapter) allocates G0/G1 for argument depths
1/2; C (the `maker` adapter) allocates G2/G3 for body depths 0/1, then G4/G5
for argument depths 1/2; B (the callback adapter invoked by `d6()`) allocates
G6/G7 for argument depths 1/2. `apply_adapter` allocates markers before
marking the argument value, so G6/G7 are consumed even though scalar `()` does
not retain them. After the callback returns its closure, the relevant carried
markers are G0-G5. Calls decrement positive depths; forcing the marked effect
thunk re-enters marker frames, and frame exit preserves request guard and
carried-guard data in the implementation. The initial carried G0 exposure
snapshot is empty in this root; later snapshots reflect guards active before
each marker frame, rather than every previously allocated ID. Re-entry of an
existing marker does not allocate a new ID. The plain catch has no marker
frame, so the frozen implementation's missing-handler path selects a carried
guard and skips the arm; the root host then reports the unhandled request.
This is source-derived symbolic execution, not an instrumented runtime log,
and the own-path skip remains in conflict with the marker specification.
Independent source audit confirmed the G6/G7 allocation and that outer
marker stripping does not remove markers nested inside returned adapters or
thunks. The trace is limited to frozen mono-runtime; it proves neither VM
parity nor declarative handler eligibility.

A second control makes the callback itself return the effectful closure:

```yu
my make_rejecter() = \_ -> choose::reject()
my maker(f: () -> [choose] (int -> [choose] int)) = f()
my delayed = maker(make_rejecter)
my caller(): [] int = catch delayed(0):
  choose::reject(), k -> k 3
  v -> v
```

The frozen checker accepts it; `--poly-raw` again gives `maker`, `delayed`,
and `caller` pure result-effect slots, and the interpreter reports an
unhandled `choose::reject`. Its runtime IR shows callback markers at depths 1
and 2, plus returned maker-body markers at depths 0 and 1. This is a
distinguishing lowering control for callback-result transport, not yet a
runtime log of marker ids, frame exits, resumption, and catch skipping. The
successor's dynamic eligibility remains unresolved; the coarse effect
candidate's pure-annotation rejection does not depend on that choice.

The matched absent-contract control rejects the explicit pure caller with an
effect-filter mismatch. With the caller annotation inferred instead, the
absent-contract program retains `[choose]` in `delayed` and `caller`, and the
caller handler returns `[3]`. The concrete-contract version with the caller
annotation inferred has `Bot` result effects and fails at runtime with the
unhandled request. These outcomes isolate the contract-dependent difference
on this returned-callback shape; they still do not choose the successor's
handler-eligibility rule.

Compatibility consequence: the successor cannot adopt Oracle's complete
combination of pure returned-closure effects and pure caller acceptance as a
validated rule. If `choose` escapes the receiving function, the returned
closure's latent effect must retain it. Whether the surrounding pure caller is
then rejected is no longer dependent on the unresolved eligibility rule for
the current coarse candidate. Its shallow handler assigns the whole
pre-handler effect `E` to `k`; the arm `k 3` therefore contributes `choose` to
the arm-effect union, which runs outside the same shallow catch. If the request
is ineligible, `choose` also remains in `E \ M`; if eligible, the resumed
continuation summary still contributes it through the arm. Thus this candidate
rejects the pure caller annotation under either eligibility outcome. This is
a conservative approximation choice, not a claim that the exact one-request
trace contains an outward request or that the Oracle program is semantically
well-typed. The candidate acceptance delta is concrete: Oracle `check`
accepts the pure caller, while the proposed compositional bound rejects it;
Oracle's runtimes report the request unhandled. Whether a more precise
abstraction can soundly accept it remains open. No final successor rule is
selected until soundness and least-derivability relative to the chosen
abstraction are proved.

Focused commands used the frozen checkout's prebuilt CLI and sources in
`/tmp/yulang-intrusion-*`:

```text
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-capture-escape.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-capture-escape.yu
yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-capture-escape.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-direct-closure-control.yu
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-direct-closure-inferred.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-capture-escape-absent-inferred.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-absent-inferred.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-absent-inferred.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-capture-escape-absent-inferred.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-capture-escape-wildcard-inferred.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-wildcard-inferred.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-wildcard-inferred.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-capture-escape-wildcard-inferred.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-capture-escape-empty-inferred.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-empty-inferred.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-empty-inferred.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-capture-escape-empty-inferred.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-capture-escape-concrete-inferred.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-concrete-inferred.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-concrete-inferred.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-capture-escape-concrete-inferred.yu
yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-capture-escape-concrete-inferred.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-returning-callback-control.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-returning-callback-control.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-returning-callback-control.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-returning-callback-control.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-returning-callback-absent.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-returning-callback-absent-inferred.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-returning-callback-absent-inferred.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-returning-callback-absent-inferred.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-returning-callback-absent-inferred.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-returning-callback-concrete-inferred.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-returning-callback-concrete-inferred.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-returning-callback-concrete-inferred.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-returning-callback-concrete-inferred.yu
```

The callback/closure fixture's check and dump exit 0; both runtime commands
exit 1 with `yulang.unhandled-effect`. The direct pure-annotation control exits
1 with an effect filter mismatch; its inferred control exits 0 and returns
`[3]`. Each no-contract/wildcard/empty inferred variant checks successfully
and returns `[3]`; the concrete `[choose]` inferred variant checks but both
runtimes fail with `yulang.unhandled-effect`. This is Oracle characterization,
not an implementation test.

## Parameterized one-step soundness lemma

The coarse row rule can be isolated from the still-open hygiene semantics by
parameterizing the handler transformer with two independent predicates:

```text
Covered(H, activation, operation)
Visible(request, H, activation)
```

`Visible` must refer to the request's provenance and the active handler
activation. It is not defined by family equality. A configuration `κ` records
the active activation and relevant provenance/guard state. Keep the exact
request occurrence on each trace path; do not aggregate different paths that
share a family into one node-local visibility value.

For a request tree `C`, write `May(C)` for a sound family-set upper bound on
the union of supports of all finite traces through `C`, including every
continuation suffix for every operation result. This finite-trace definition
also applies when recursion makes the request tree infinite. Assume each arm
judgment soundly summarizes its immediate execution for arbitrary calls to
raw `k`, with `k` assigned latent row `May(C)`. If an arm returns a callable
or thunk that captures `k`, its result-value typing must separately preserve
that latent row. The following simulation targets immediate trace effects:

The source-grounded eligibility hypothesis above decomposes the predicates:

```text
Eligible(q, H, κ) = Active(H, κ)
                    and Covered(H, κ, q.operation)
                    and Visible(q, H, κ)

Visible(q, H, κ) =
    for every boundary b in q.ordered_boundary_lineage:
        outside(H.activation, b, κ)
        or matching_grant(b, q.family, H.activation, κ)
    and no_other_active_boundary_masks(q, H, κ)
```

Here `κ` must contain the active handler identities, the specific receiving
activation and its nesting relation to each handler, the ordered request
lineage, and explicit contract evidence. `outside` is evaluated at the
request's current activation, including closure re-entry; it is not inferred
from the source location where a closure was created. These predicates remain
conditional because the successor's scope transport and runtime correspondence
are unproved. If any premise cannot be established, `Visible` is false for
subtraction purposes and the family remains in the bound.

```text
T_{H,κ}(Return(v)) = value_arm(v)

T_{H,κ}(Request(q, k)) = operation_arm(q, k)
    if Eligible(q, H, κ)

T_{H,κ}(Request(q, k)) = Request(q, x -> T_{H,κ'}(k(x)))
    otherwise
```

In the forwarded case, `κ'` ranges over the successor configurations allowed
when that request is resumed by its surrounding context. Those transitions
are part of the still-open source semantics.

Let `Reach(H, C, κ0)` contain every request/activation/provenance
configuration reachable from the initial configuration `κ0` while evaluating
the transformed tree, including arm execution, raw-continuation calls, tails
reached after any allowed operation result, and handler re-entry induced by
forwarding. Let `Offered(H, C, κ0)` be the subset of request configurations
actually offered to this handler while evaluating the scrutinee: include the
initial scrutinee path and suffixes revisited after a forwarded request is
resumed, but exclude raw-continuation suffixes executed by a matching operation
arm because that continuation is not wrapped by this handler. Let `A(H, C,
κ0)` be one uniform upper bound for value and operation arm effects across
every applicable handler configuration in `Reach(H, C, κ0)`, with raw `k`
assigned latent `May(C)`. Let `Drop(H, C, κ0)` be a proof-carrying set of
families, not a function of the family row alone. A family `f` may enter
`Drop(H, C, κ0)` only if every configuration in `Offered(H, C, κ0)` for a
request of family `f` is covered and visible at that activation, with positive
evidence that the handler is active. This quantification must account for
forwarding: an outer handler may resume a forwarded continuation zero, one,
or multiple times, producing different configurations. A row/provenance
coupling premise must classify each contribution to `May(C)` by route: a
contribution that may be in `Offered` needs a covering request fact or
unknown; a contribution confined to a matched raw continuation is instead
covered by the latent `May(C)` assigned to `k` and charged to the arm/value
summary when invoked or exported. If a contribution may follow both routes,
both obligations apply. The abstract result is:

```text
(May(C) \ Drop(H, C, κ0))
    ∪ A(H, C, κ0)
```

### Conditional statement

Assume:

1. `May(C)` includes the request at each node and all suffix requests for every
   operation result, with the bound valid for every finite trace.
2. The arm judgments soundly bound immediate arm execution with raw `k` typed
   at latent effect `May(C)`, including any finite number of invocations.
3. `Drop(H, C, κ0)` excludes every family that occurs at any uncovered or
   ineligible request configuration in `Offered(H, C, κ0)`, including
   configurations reached after forwarding and outer resumption. Requests in
   raw-continuation suffixes of matched operations are instead bounded through
   `May(C)` at `k` whenever an arm calls or exports it.

Then every immediate family on every finite trace of `T_{H,κ0}(C)` is in the
abstract result above. This statement covers recursive/infinite request trees
by considering each finite trace prefix. It is conditional: it does not prove
`Visible`, validity or existence of `Drop` certificates, sound arm judgments,
least derivability, or principal schemes. To extend this immediate-trace
result to higher-order soundness, prove separately that every returned
callable/thunk capturing `k` preserves its latent row and visibility evidence
in its result value type.

### Proof sketch

Induct on finite trace length with the uniform invariant that every reachable
transformed suffix from `Reach(H,C,κ0)` is bounded by the original result
`May(C) \ Drop(H,C,κ0) ∪ A(H,C,κ0)`.

- For `Return(v)`, the transformed trace evaluates the value arm, whose
  immediate families are in the value-arm term of the abstract result.
- For an uncovered or ineligible request `q` of family `f`, premise 3 gives
  `f ∉ Drop(H,C,κ0)`. The forwarded request itself is in
  `May(C) \ Drop(H,C,κ0)`. Its continuation resumes in a configuration in
  `Reach(H,C,κ0)`; the remaining finite trace is shorter, so the induction
  hypothesis using the same original global bound covers its later families.
- For a covered and eligible request, the transformed trace evaluates the
  matching operation arm. The uniform arm judgment in `A(H,C,κ0)` bounds its
  immediate effects, including any raw `k` calls. Every suffix reached by
  such a call is bounded by `May(C)` under premise 1 and included through
  `k`'s latent effect in the same arm summary. The shallow rule does not apply
  `H` again to that raw continuation.

The compiler-referee delta review found no finite-trace counterexample under
these conditions. It noted that the induction must retain the original global
bound and arm union across every reachable suffix, rather than recomputing a
new bound for each suffix. The sketch now states that uniform invariant and
quantifies arm bounds over all reachable activations. This is a wording-level
repair, not a proof certification. In particular, a returned closure's later
invocation needs the separate value-correspondence proof; immediate trace
inclusion alone does not establish higher-order soundness. Nor does this proof
establish a least-solution property or principal schemes.

The quantifier in `Drop` exposes an important limitation: a family-set row
alone cannot prove that *all* contributing requests are visible. A solver
would need to retain enough occurrence/path evidence to justify a drop, or
conservatively leave the family residual whenever that evidence is absent.
This is an abstract proof requirement, not a choice of graph representation.
The unresolved closure-escape and helper-composition cases determine whether
such evidence can be transported soundly.

#### Row-to-offer coupling is still a separate construction obligation

The conditional lemma above needs route-sensitive coupling, not equality
between abstract row membership and a concrete offer. An effect contribution
can reach this handler on the initial or a forwarded path, be confined to a
matched raw continuation, or have both possibilities after a join. An
open/imported or otherwise unclassified contribution also needs an unknown
route. The concrete request-annotation result contract remains a separate
upper filter and is not itself a lower-row contribution.

There is a concrete counterexample to the earlier blanket coupling premise.
Take distinct families `P` and `Q` and the tree
`C = Request(P.ping, (), λ_. Request(Q.choose, (), λ_. Return(v)))`. Let `H`
cover both operations and its `P.ping` arm invoke raw `k`. Then
`May(C) = {P,Q}`, but only `P.ping` is offered to `H`; the raw continuation
emits `Q.choose` outside `H`. This is the distinct-family case in Lemma 3 of
`2026-09-30-intrusion-shallow-handler-trace-calculus.md`. The `Q`
contribution is included through
`k : May(C)` in the arm bound `A` when resumed. Thus the prior blanket premise
requiring every family in `May(C)` to appear in `Offered(H,C)` was too
strong. The conditional handler soundness formula is unchanged: raw suffixes
remain accounted for through `k`, while `Drop` quantifies only over offers to
this handler.

Route coupling instead classifies each *contribution* (not just each family)
as current/forwarded offer, matched-raw-continuation latent effect, or unknown.
Current/forwarded routes need possible-offer facts at every compatible
handler slot. Raw-only routes need preservation in `k`'s latent row and in
every arm or value type that invokes or exports `k`. Mixed routes retain both
obligations. An unclassified possible offer widens to unknown/top so it cannot
be subtracted. This uses no continuation-use count. The witness is an
inference about the candidate's proof premise, not a new Oracle behavior or a
counterexample to the conditional effect formula. Uniform transfer, finite
quotient construction, and source-constraint correspondence remain open.

##### Handler-relative route alternatives (candidate representation)

The route classification can be made explicit without identifying route
support with exact trace support. For each static handler slot `h`, abstract
family contribution `c`, and possible activation class, retain a set of
handler-relative alternatives:

```text
OfferNow(operation, origin, lineage, scope_evidence)
OfferForwarded(operation, origin, lineage, scope_evidence)
RawOnly(matched_operation, raw_k, latent_effect_destination)
Unknown
```

`OfferNow` and `OfferForwarded` describe requests that may be presented to
`h`; the latter includes suffixes re-entering `h` after an outer context
resumes a forwarded continuation. `RawOnly` means that this contribution is
reachable solely through the raw continuation of a request matched by this
activation of `h`, without automatically reinstating that activation. It is
not a global property of the contribution: classify it separately relative to
outer or independently installed handlers. A join unions alternatives. If
lost correlation prevents ruling out another route, add `Unknown`; a mixed
offer/raw contribution therefore keeps both the offer and latent obligations.
These labels denote sets of dynamic activations, not dynamic identities; equal
source-site labels alone never establish equal activation or scope.

For a finite row, `f` may be removed at `h` only when the route evidence is
complete for every contribution of `f` and every represented activation:
every offer alternative is covered and visible, every raw-only alternative
is preserved through `k`'s latent row and any value that invokes or exports
it, and no contribution is unknown or unclassified. The raw-only condition
does not create an offer to `h`; a route that may be both offered and reached
through raw `k` must satisfy both conditions. This is a finite proof-object
shape, not a construction theorem: completeness, sound transfer through
forwarding and higher-order values, and a finite activation quotient remain
open. If source constraints cannot maintain this route distinction, retain
unknown/top rather than infer a drop from the family row.

Exact finite-trace semantics remains the reference used to prove this
abstraction sound. Its row need not equal exact trace support: the shallow
one-request/resume example can retain a family in `k`'s latent row even when
the concrete suffix has no request. No continuation-use count, linear or
affine continuation typing, or exact continuation-sensitive inference is
required by this candidate. Any principality claim concerns least solutions
of the explicitly chosen compositional abstraction, after source derivability
and the fixed-`Drop` transfer are proved equivalent; it does not claim a least
exact-trace row.

A source-derivation audit for the eventual construction should classify every
effect-family contribution before closure, rather than infer origins from the
solved row alone:

| Source of a family bound | Required offer/provenance action |
|---|---|
| Direct operation request | Add its exact family, operation, and origin fact before handler matching. |
| Handler clause operation coverage and scrutinee upper `[handled; residual]` | Track the mentioned operations as coverage or an upper constraint only. Mere mention creates neither a scrutinee request offer nor `Drop` evidence. This candidate disallows a direct positive contribution to `May(C)`; source-to-constraint proof must show that the upper bound constrains rows without generating effect support. If the solver cannot maintain this separation, revise the representation or candidate semantics; do not turn coverage metadata into a fabricated offer. |
| Known call, force, or callable value | Include offers from every target admissible under the current type/effect assignment; preserve latent facts across storage and re-entry. |
| Open/imported callable or row | Add unknown/top offer facts at every compatible handler unless a closed interface summary bounds them. |
| Higher-order formal or callback argument | Quantify over all admissible supplied values, or use an interface summary/top; the annotation's family set alone does not identify the concrete request origin or target. |
| Row join or whole-scrutinee continuation summary | Preserve route tags by contribution: current/forwarded offer, matched raw-continuation latent effect, or unknown. A mixed join keeps all possible routes; raw-only contributions flow through `k`/captured values, not a fabricated offer to the matching handler. |
| Forwarded request resumed by an outer context | Re-enter the captured handler wrapper and include the resulting offers; raw matched-continuation resumption remains separately summarized through `k`. |
| Value and operation arm effects | Count these effects in `A`; track requests emitted by the arms for outer handlers. An arm request is not an offer to this shallow handler's scrutinee `Drop`. |
| Result-position effect annotation/filter | Constrain the inferred result row but do not invent an effect origin or prove that an admitted family is offered. Callable interface latent bounds belong to the call/formal source rules above; absent target offer proof, retain unknown/top. |

This table is a proof checklist, not a transfer definition. In particular,
"known call" requires a target superset uniform over admissible assignments,
and higher-order quantification may need `TopCall#`; either can change final
acceptance. It remains to prove the table's transfers preserve the source
request semantics and that their resulting origin set is finite (or has a
sound finite quotient). This candidate excludes handler coverage as a direct
positive source of successor `May(C)`; whether source lowering and solver
constraints can implement that separation is unresolved. This checklist does
not select a transfer or authorize implementation.

The direct exact-trace lemma in
`2026-09-30-intrusion-shallow-handler-trace-calculus.md` isolates the first
handler-coverage table row: covered-operation metadata does not itself emit a
request. Its proof inspects return, matched-request, and forwarded-request
transformer cases. It does not resolve Oracle row lowering or whether a
successor coverage upper row contributes to an effect slot. The
compiler-referee closure of the table is therefore record-level closure of
the classification finding only; source-to-constraint correspondence and
successor transfer semantics remain open. Arm-emitted requests belong in `A`
and may be seen by outer handlers, not this scrutinee's `Drop`.

#### Candidate consequence for the declarative effect rule

For this candidate only, the exact operation set in a handler clause is
coverage metadata for `Covered(H, operation)`; its family projection can help
index candidates, but is not a lower source for `May(C)` or an `Offered` fact.
The scrutinee's effect summary is derived from its computation and
callable/latent sources; the handler transforms that summary using coverage
and visibility, and arm execution contributes separately through `A`. A
family may enter `Drop` only if every possible operation occurrence and offer
of that family is covered and visible. The exact-trace Lemma 4 establishes
that clause coverage emits no concrete request; excluding coverage as a
positive source in this coarser abstraction is a candidate rule choice
consistent with the lemma, not a consequence forced by it. Other abstraction
steps may still add spurious families, which require route provenance (offer,
raw-latent, or unknown/top). A successor constraint lowering that places the
handler's coverage upper `[handled; residual]` in the positive source of
`May(C)` would not implement this candidate rule. Its source-to-constraint
proof must show that the upper bound constrains admissible rows without
creating request or offer evidence. If the solver representation cannot
maintain that distinction, the representation or supported rule must be
revised before claiming soundness or principality.

This is a candidate successor rule inferred from the declared trace semantics,
not a fact about Oracle routing and not an approved implementation decision.
The exact impact on supported final acceptance and the lowering/solver
correspondence remain open.
